/*
    mm.c

    Name: Dev Patel

    My solution uses a Segregated List and Best-Fit placement policy to store and find free blocks respectively.
    Moreover, an Immediate-Coalescing policy is used.

    The heap structure contains an alignment padding at first, followed by a prologue block. Then comes the blocks
    in the middle, ended by an epilogue block. Its structure is shown as follows:

            heap_listp
               |                                                        
               V            <-----prologue------>                         <-epilogue->                       
               ---------------------------------------------------------------------- 
              |  padding   |  header  | footer   |         blocks        |  header   |
               ----------------------------------------------------------------------
                                                     

    Allocated and Free blocks have a different structure. An allocated block has a basic header and footer that
    stores the size and alloc bit, a payload area where the allocated memory is stored, and an optional padding.
    A free block has the same header and footer, but the first and the second words of its payload store
    information about the next and previous free blocks respectively. The structure of these blocks is shown as follow:
    
                  Allocated Block                                 Free Block    
                -------------------                           -------------------
               | H   size/alloc    |                         | H   size/alloc    |
               |-------------------|                         |-------------------|
               |                   |                         |  next free block  |            
               |                   |                         |-------------------|
               |      payload      |                         |  prev free block  |
               |                   |                         |-------------------|
               |-------------------|                         |                   |            
               | padding(optional) |                         |                   |
               |                   |                         |                   |
               |-------------------|                         |-------------------|
               | F   size/alloc    |                         | F   size/alloc    |                     
                -------------------                           -------------------

    All free blocks are stored in a seglist, which is an array of freelists of different classes. 12 classses of
    freelists have been defined. Each class of freelists has a range of payload size, for example: 0-32, 32-64, 64-128,
    and so on.
*/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <stdint.h>
#include <stdbool.h>

#include "mm.h"
#include "memlib.h"

/*
 * If you want to enable your debugging output and heap checker code,
 * uncomment the following line. Be sure not to have debugging enabled
 * in your final submission.
 */
// #define DEBUG

#ifdef DEBUG
// When debugging is enabled, the underlying functions get called
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#else
// When debugging is disabled, no code gets generated
#define dbg_printf(...)
#define dbg_assert(...)
#endif // DEBUG

// do not change the following!
#ifdef DRIVER
// create aliases for driver tests
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mm_memset
#define memcpy mm_memcpy
#endif // DRIVER

#define ALIGNMENT 16

static const int WSIZE = 8; // Word and header/footer size
static const int DSIZE = 16; // Double word size
static const int CHUNKSIZE = (1<<12); // Used to extend heap by this amount
static const int SEGLIST_CLASSES = 12; // Number of freelists of various size range in seg_listp

/*********  Global Pointers  *********/
static char* heap_listp; // pointer to the prologue block
static char* seg_listp; // pointer to the seglist

/************  Helper Functions begin  ************/

// Pack a size and allocated bit into a word
static size_t PACK(size_t size, size_t alloc) {
    return (size_t)((size) | (alloc));
}

// Read a word at address p
static size_t GET(void* p) {
    return (*(size_t *)(p));
}

// Write a word at address p
static void PUT(void* p, size_t val) {
    (*(size_t *)(p) = (val));
}

// read the size field from address p
static size_t GET_SIZE(void* p) {
    return (GET(p) & ~0x7);
}

// Read the alloc field from address p
static size_t GET_ALLOC(void* p) {
    return (GET(p) & 0x1);
}

// Address of the header pointer
static char* HDRP(char* bp) {
    return ((char *)(bp) - WSIZE);
}

// Address of the footer pointer
static char* FTRP(char* bp) {
    return ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE);
}

// Address of the next block pointer
static char* NEXT_BLKP(char* bp) {
    return ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)));
}

// Address of the previous block pointer
static char* PREV_BLKP(char* bp) {
    return ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)));
}

// Read the alloc field of the previous block, ie. find if the prev block if free or allocated
static size_t PREV_ALLOC(void *p) {
    return GET(p) & 0x2;
}

// Write a pointer at address p
static void PUT_ADDR(void* p, void* val) {
    (*(size_t *)(p)) = (size_t)val;
}

// Returns the address of the next free block
static char* NEXT_FREE_ADDR(void *bp) {
    return (char*)(bp);
}

// Returns the address of the previous free block
static char* PREV_FREE_ADDR(void *bp) {
    return (char *)(bp) + WSIZE;
}

// Determines the index of freelist from seg_listp where size belongs
static int get_segclass_ind(size_t size) {
    if (size <= 32)
        return 0;
    else if (size <= 64)
        return 1;
    else if (size <= 128)
        return 2;
    else if (size <= 256)
        return 3;
    else if (size <= 512)
        return 4;
    else if (size <= 1024)
        return 5;
    else if (size <= 2048)
        return 6;
    else if (size <= 4096)
        return 7;
    else if (size <= 8192)
        return 8;
    else if (size <= 16384)
        return 9;
    else if (size <= 32768)
        return 10;
    else // size>32768
        return 11;
}

// Rounds up to the nearest multiple of ALIGNMENT
static size_t align(size_t x) {
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}

// Adds a block to seg_listp at appropriate index, given a block pointer and size
static void seglist_add(char* bp, size_t size) {
    int ind = get_segclass_ind(size);
    char* class = seg_listp + ind*WSIZE; // pointer to the appropriate class of freelist
    char* first_blk = (char *)GET(class); // address of the first block in that class
    
    if (first_blk) { // if that class of freelist is not empty
        PUT_ADDR(class, bp); // add the new free block before the first element of that class
        PUT_ADDR(NEXT_FREE_ADDR(bp), first_blk);
        PUT_ADDR(PREV_FREE_ADDR(bp), NULL);
        PUT_ADDR(PREV_FREE_ADDR(first_blk), bp);
    }
    else { // if that class of freelist is empty
        PUT_ADDR(class, bp); // add the new free block as the first element of that class
        PUT_ADDR(NEXT_FREE_ADDR(bp), NULL); 
        PUT_ADDR(PREV_FREE_ADDR(bp), NULL);
    }
}

// Removes a block from seg_listp, given a block pointer and size
static void seglist_delete(char *bp, size_t size) {
    int ind = get_segclass_ind(size);

    // address of next and previous free blocks
    char* next = (char *)GET(NEXT_FREE_ADDR(bp)); 
    char* prev = (char *)GET(PREV_FREE_ADDR(bp));
    
    if (next && !prev) { // if the block to be deleted is the first block in that class
        PUT_ADDR(seg_listp + ind*WSIZE, next);
        PUT_ADDR(PREV_FREE_ADDR(next), NULL);
    }
    else if (!next && prev) { // if the block to be deleted is the last block in that class
        PUT_ADDR(NEXT_FREE_ADDR(prev), NULL);
    }
    else if (next && prev) { // if the block to be deleted is somewhere in the middle of that class
        PUT_ADDR(PREV_FREE_ADDR(next), prev);    
        PUT_ADDR(NEXT_FREE_ADDR(prev), next);
    }
    else { // if the class is empty  
        PUT_ADDR(seg_listp + ind*WSIZE, NULL);
    }
}

// Coalesces or merges adjacent free blocks of the given block pointer, given a block pointer
static void *coalesce(void *bp) {
    size_t prev_alloc = PREV_ALLOC(HDRP(bp)); // alloc bit of previous block
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // alloc bit of next block
    size_t size = GET_SIZE(HDRP(bp));

    /*delete the adjacent free blocks from seglist, then increment the size accordingly, then update the header 
    and the footer, and finally add the new free block to seglist.*/

    if (prev_alloc && next_alloc) { // if both prev and next are not free
        return bp;
    }
    else if (prev_alloc && !next_alloc) { // if next is free
        seglist_delete(bp, size);
        seglist_delete(NEXT_BLKP(bp), GET_SIZE(HDRP(NEXT_BLKP(bp))));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, prev_alloc));
        PUT(FTRP(bp), GET(HDRP(bp)));
        seglist_add(bp, size);
    }
    else if (!prev_alloc && next_alloc) { // if prev is free
        seglist_delete(bp, size);
        seglist_delete(PREV_BLKP(bp), GET_SIZE(HDRP(PREV_BLKP(bp))));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, PREV_ALLOC(HDRP(PREV_BLKP(bp)))));
        PUT(FTRP(PREV_BLKP(bp)), GET(HDRP(PREV_BLKP(bp))));
        seglist_add(PREV_BLKP(bp), size);
        bp = PREV_BLKP(bp);
    }
    else { // if both prev and next are free
        seglist_delete(bp, size);
        seglist_delete(PREV_BLKP(bp), GET_SIZE(HDRP(PREV_BLKP(bp))));
        seglist_delete(NEXT_BLKP(bp), GET_SIZE(HDRP(NEXT_BLKP(bp))));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, PREV_ALLOC(HDRP(PREV_BLKP(bp)))));
        PUT(FTRP(PREV_BLKP(bp)), GET(HDRP(PREV_BLKP(bp))));
        seglist_add(PREV_BLKP(bp), size);
        bp = PREV_BLKP(bp);
    }
    return bp;
}

// Increases the heap size, given the amount of increment
static void *extend_heap(size_t words) {
    char *bp;
    size_t size = align(words); // Maintain alignment
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    PUT(HDRP(bp), PACK(size, PREV_ALLOC(HDRP(bp)))); // Free block header
    PUT(FTRP(bp), GET(HDRP(bp))); // Free block footer
    seglist_add(bp, size); // 
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // New epilogue header
    return coalesce(bp); // Coalesce if the previous block was free

}

// Helper function for find_fit.
// Searches for a free block in the given freelist using Best-Fit policy, given a freelist and requested size
static void *seglist_search(size_t list, size_t size) {
    char *curr = (char *)GET(seg_listp + list*WSIZE); // address of first block in the given freelist
    char *best = NULL; // best free block
    size_t diff = 0;
    while (curr) { // iterating through the freelist
        if (size <= GET_SIZE(HDRP(curr))) { // if requested size is less than the size of the current block
            if (!best || diff>(GET_SIZE(HDRP(curr))-size)) {
                diff = GET_SIZE(HDRP(curr))-size;
                best = curr;
                if (diff == 0)
                    return best;
            }
        } 
        curr = (char *)GET(NEXT_FREE_ADDR(curr));
    }
    return best;
}

// Actually finds a free block suitable, given the requested size
static void *find_fit (size_t asize) {
    void *bp;
    int ind = get_segclass_ind(asize);
    // search for best-fit free block in all freelists that have a class size greater than i
    for (int i=ind; i<SEGLIST_CLASSES; i++) {
        bp = seglist_search(i, asize);
        if (bp)
            return bp;
    }
    return NULL; // No fit
}

// Allocates and places a block into the heap according to the requested size. Also, split if necessary
static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2*DSIZE)) { // split block if possible
        seglist_delete(bp, csize);
        // reset size and alloc bit of resulted allocated block from the split
        PUT(HDRP(bp), PACK(asize, PACK(PREV_ALLOC(HDRP(bp)), 1)));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 2)); // update header of resulted free block from the split
        PUT(FTRP(bp), PACK(csize-asize, 2)); // update footer of resulted free block from the split
        seglist_add(bp, csize-asize); // add splitted free block to seglist
    }
    else { // no split
        seglist_delete(bp, csize);
        PUT(HDRP(bp), PACK(csize, PACK(PREV_ALLOC(HDRP(bp)), 1))); // update header of allocated block
        PUT(HDRP(NEXT_BLKP(bp)), PACK(GET(HDRP(NEXT_BLKP(bp))), 2)); // update footer of allocated block
    }
}

/************  Helper Functions end  ************/

/*
 * mm_init: returns false on error, true on success.
 */
bool mm_init(void) {
    // request memory to fit all classes of seglist in memory
    if ((seg_listp = mem_sbrk(SEGLIST_CLASSES*WSIZE)) == (void *)-1) {
        return false;
    }
    // each class of the seglist points to null as they are empty during initialization
    for (int i=0; i<SEGLIST_CLASSES; i++) {
        PUT_ADDR(seg_listp + (i*WSIZE), NULL);
    }
    // create the initial empty heap
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return false;
    PUT(heap_listp, 0); // Alignment padding
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); // Prologue header
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); // Prologue footer
    PUT(heap_listp + (3*WSIZE), PACK(0, PACK(2,1))); // Epilogue header
    heap_listp += (4*WSIZE);

    // extend the empty heap with a free block of CHUNKSIZE bytes
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return false;
    return true;
}

/*
 * malloc
 */
void* malloc(size_t size) {
    if (size <= 0)
        return NULL;

    size_t asize = align(size + DSIZE); // Maintain ALIGNMENT
    char *bp = find_fit(asize); // get a best-fit free block

    if (bp) {
        place(bp, asize); // place that free block in the heap
        return bp;
    }
    if ((bp = extend_heap(asize)) == NULL) // extend the heap if not fit found
        return NULL;
    place(bp, asize); // now try placing
    return bp;
}

/*
 * free
 */
void free(void* ptr) {
    if (!ptr)
        return;

    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, PREV_ALLOC(HDRP(ptr))));
    PUT(FTRP(ptr), GET(HDRP(ptr)));     
    PUT(HDRP(NEXT_BLKP(ptr)), PACK(GET_SIZE(HDRP(NEXT_BLKP(ptr))), GET_ALLOC(HDRP(NEXT_BLKP(ptr)))));
    seglist_add(ptr, size);
    coalesce(ptr); // immediate coalescing policy
}

/*
 * realloc
 */
void* realloc(void* oldptr, size_t size) {
    size_t size_old = GET_SIZE(HDRP(oldptr));
    if (!oldptr) // if oldptr is null
        return malloc(size); // call is equivalent to malloc
    else if (size == 0) { // if size is zero
        free(oldptr); // call is equivalent to free
        return NULL;
    } 
    else { // oldptr is not null, so must have been returned by earlier calls to malloc
        void *ptr = malloc(align(size));
        if (!ptr)
            return ptr;
        if (size < size_old)
            memcpy(ptr, oldptr, size);
        else 
            memcpy(ptr, oldptr, size_old);
        free(oldptr);
        return ptr;
    }
}

/*
 * calloc
 * This function is not tested by mdriver, and has been implemented for you.
 */
void* calloc(size_t nmemb, size_t size) {
    void* ptr;
    size *= nmemb;
    ptr = malloc(size);
    if (ptr) {
        memset(ptr, 0, size);
    }
    return ptr;
}

/*
 * Returns whether the pointer is in the heap.
 * May be useful for debugging.
 */
static bool in_heap(const void* p) {
    return p <= mm_heap_hi() && p >= mm_heap_lo();
}

/*
 * Returns whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void* p) {
    size_t ip = (size_t) p;
    return align(ip) == ip;
}

/*
 * mm_checkheap
 */
bool mm_checkheap(int lineno) {
#ifdef DEBUG

    size_t seg_free_ct = 0; // count of free blocks in seglist
    size_t heap_free_ct = 0; // count of free blocks in the heap

    dbg_printf("Currect heap size: %zu \n First byte of the heap: %p \n Last byte of the heap %p \n", mm_heapsize(),
               mm_heap_hi(), mm_heap_lo());
    
    // Invariant 1: Every block in the free list should be marked as free
    for (int i=0; i<SEGLIST_CLASSES; i++) {
        char *curr = (char *)GET(seg_listp + i*WSIZE); // address of first block in i_th freelist
        while (curr) {
            seg_free_ct += 1;
            if (GET_ALLOC(HDRP(curr))) { // if there are any allocated blocks in this freelist
                dbg_printf("Freelist at class index %d has an allocated block. Look at line %d", i, lineno);
                return false;
            }
            curr = (char *)GET(NEXT_FREE_ADDR(curr));
        }
    }

    // Invariant 2: Every free block should actually be in the free list
    char *bp1 = heap_listp;
    while (bp1 && GET_SIZE(HDRP(bp1))!=0) { // iterate through entire heap
        if (!GET_ALLOC(HDRP(bp1)))
            heap_free_ct += 1;
        bp1 = NEXT_BLKP(bp1);
    }
    if (heap_free_ct != seg_free_ct) {
        dbg_printf("Heap and freelist don't have same number of free blocks. heap_count is %zu and freelist_count is %zu. Look at line %d.", 
                   heap_free_ct, seg_free_ct, lineno);
        return false;
    }


    // Invariant 3:  The pointers in the free list should point to valid free blocks
    for (int i=0; i<SEGLIST_CLASSES; i++) {
        char *curr = (char *)GET(seg_listp + i*WSIZE); // address of first block in i_th freelist
        while (curr) {
            if (GET_SIZE(HDRP(curr))==0 || curr>(char *)mm_heap_hi() || curr<(char *)mm_heap_lo()) { // invalid conditions
                dbg_printf("Freelist at class index %d has an invalid pointer %p. Look at line %d", i, curr, lineno);
                return false;
            }
            curr = (char *)GET(NEXT_FREE_ADDR(curr));
        }
    }

    // Invariant 4: Allocated blocks should never overlap
    char *bp2 = heap_listp;
    while (bp2 && GET_SIZE(HDRP(bp2))!=0) { // iterate through entire heap
        if (GET_ALLOC(HDRP(bp2))) {
            size_t size = GET_SIZE(HDRP(bp2));
            if (bp2+size-WSIZE >= NEXT_BLKP(bp2)) { // overlap
                dbg_printf("Block %p overlaps with the next block %p. Look at line %d.", bp2, NEXT_BLKP(bp2), lineno);
                return false;
            }
        }
        bp2 = NEXT_BLKP(bp2);
    }

    // Invariant 5: The pointers in a heap block should point to valid heap address
    char *bp3 = heap_listp;
    while (bp3 && GET_SIZE(HDRP(bp3))!=0) { // iterate through entire heap
        if (!bp3 || bp3>(char *)mem_heap_hi() || bp3<(char *)mem_heap_lo()) { // invalid conditions
            dbg_printf("Heap has an invalid pointer %p. Look at line %d", bp3, lineno); 
            return false;
        }
        bp3= NEXT_BLKP(bp3);
    }

#endif // DEBUG
    return true;
}

/*

Giving Credit:

Basic structure of the allocator implemented in this malloclab has been adapted from the CSAPP (Computer Systems: A 
Programmer's Perspective, 3/E) textbook by Randal E. Bryant and David R. O'Hallaron.

Initial helper functions --PACK, GET, PUT, GET_ALLOC, GET_SIZE, HDRP, FTRP, NEXT_BLKP, PREV_BLKP-- have been referred from
the textbook.

Main helper functions --coalesce, extend_heap, find_fit, place-- have also been implemented from the textbook and then
modified according to the needs of a seglist.

Allocator functions --init, malloc, free-- have been implemented in a similar way like the main helper functions.

*/












