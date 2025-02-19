/* THE FOLLOWING MALLOC USES SEGREGATED FREE LISTS WITH VARYING LIST SIZE DISTRIBUTIONS

___________________________________________________________________________________

THE LIST ROOTS ARE PLACED AT THE START OF THE HEAP

AS SUCH THE FOLLOWING HEAP STRUCTURE IS INITIALIZED

[PADDING][ROOT1][ROOT2][ROOT3] ..... [ ROOT19][PROLOGUE1][PROLOGUE2][EPILOGUE]

WITH THIS SETUP WE DO NOT NEED TO DEFINE ANY GLOBAL DATA STRUCTURES

THE CUSTOM ROOT SEARCH TABLE IS HELPFUL SINCE IT IS POSSIBLE TO
SELECT ANY ROOT AT CONSTANT TIME.
___________________________________________________________________________________


FOR SMALLER ALLOCAITON REQUESTS THE FREE LISTS ARE SEPARATED BY 2*DISZE
FOR LARGET ALLOCATION REQUESTS >256 THE LISTS ARE SPERATED BY THE POWER OF 2

DEPENDING ON THE ALLOCATION REQUESTS SIZE ONE OF THE TWO SEARCH FIT FUNCTIONS IS USED:
 ******** dense_fit()
 ******** sparse_fit()
IF NO FREE LISTS ARE AVAILABLE IN small list classes

        ----------> dense_fit() will call sparse_fit() upon return

THE SPLIT CONDITION IN THE place() function is optimized through several observation

*/

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

#define ALIGNMENT 8
#define WSIZE 4       /* Word and header/footer size (bytes) */
#define DSIZE 8       /* Double word size (bytes) */
#define CHUNKSIZE 128 /* Extend heap by this amount (bytes) */
#define BOUNDARY 256

#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define ALIGN_QSIZE(size) (((size) + 31) & ~0x1F)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define PUTP(p, ptr) (*(char **)(p) = (char *)(ptr))
#define GETP(p) (*(char **)(p))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define LOW_OFFSET(size) ((size - 32) >> 3)
#define GET_PREV(p) (*(char **)((char *)(p) + WSIZE))

static char *heap_listp;
static char *working;
static char *last_used;

static char *dense_start;
static char *root_last;
static char *start;
static char *heap_start;

static char FLAG;
static unsigned degree;

static int nearest_two(int n)
{ /*nearest two function returns the nearest ceil power of 2*/
    int num = __builtin_clz(n);
    num = 31 - num;
    if ((1 << num) == n)
    {
        return num;
    }
    else
    {
        return num + 1;
    }
}

static void *find_root(size_t size)
{ /*Fetch and return the root according to the requested size*/
    if (size < BOUNDARY)
    {
        size = ALIGN_QSIZE(size);
        last_used = dense_start + LOW_OFFSET(size);
        return GETP(last_used);
    }
    else
    {
        degree = nearest_two(size);
        if (degree > 18)
        {
            last_used = root_last;
            return GETP(last_used);
        }
        else
        {
            last_used = heap_start + degree * WSIZE;
            return GETP(last_used);
        }
    }
}

static void set_root(size_t size, void *ptr)
{ /*Fet the root the the given address*/

    if (size < BOUNDARY)
    {
        size = ALIGN_QSIZE(size);
        PUTP(dense_start + LOW_OFFSET(size), ptr);
    }
    else
    {
        degree = nearest_two(size);
        if (degree > 18)
        {
            PUTP(root_last, ptr);
        }
        else
        {
            PUTP(heap_start + degree * WSIZE, ptr);
        }
    }
}

static void *sparse_fit(size_t asize)
{ /*Find the fitting free list within the sparse free list class */
    void *bp;
    start = find_root(asize);
    while (degree <= 18)
    {
        for (bp = start; bp != NULL; bp = GETP(bp))
        {
            if (asize <= GET_SIZE(HDRP(bp)))
            {
                return bp;
            }
        }
        degree++;
        last_used += WSIZE;
        start = GETP(last_used);
    }
    for (bp = GETP(root_last); bp != NULL; bp = GETP(bp))
    {
        if (asize <= GET_SIZE(HDRP(bp)))
        {
            return bp;
        }
    }
    return NULL;
}

static void *dense_fit(size_t asize)
{ /*Find the fitting free list within the dense FERE LIST class */
    void *bp;
    start = find_root(asize);
    while (asize < BOUNDARY)
    {
        for (bp = start; bp != NULL; bp = GETP(bp))
        {
            if (asize <= GET_SIZE(HDRP(bp)))
            {
                return bp;
            }
        }
        asize += 32;
        last_used += WSIZE;
        start = GETP(last_used);
    }
    return sparse_fit(BOUNDARY);
}

static void disconnect(void *bp)
{ /*Disconnect the given FREE BLOCK   !!!CHECK FOR THE EDGE CASES!!!   */

    size_t size = GET_SIZE(HDRP(bp));
    if (GET_PREV(bp) == NULL)
    {
        if (GETP(bp) == NULL)
        {
            set_root(size, NULL);
        }
        else
        {
            PUTP(GETP(bp) + WSIZE, NULL);
            set_root(size, GETP(bp));
        }
    }
    else
    {
        if (GETP(bp) == NULL)
        {
            PUTP(GET_PREV(bp), NULL);
        }
        else
        {
            PUTP(GET_PREV(bp), GETP(bp));
            PUTP(GETP(bp) + WSIZE, GET_PREV(bp));
        }
    }
}

static void make_root(void *bp)
{ /*Use LIFO policy to insert the FREE BLOCK at the start of the appropriate free list class */

    PUTP((char *)(bp) + WSIZE, NULL);
    working = find_root(GET_SIZE(HDRP(bp)));
    PUTP(bp, working);

    if (working != NULL)
    {
        PUTP(working + WSIZE, bp);
    }
    PUTP(last_used, bp);
}

static void place(void *bp, size_t asize)
{

    size_t csize = GET_SIZE(HDRP(bp));
    size_t nsize = csize - asize;
    disconnect(bp);
    if (nsize >= 32)
    {

        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(nsize, 0));
        PUT(FTRP(bp), PACK(nsize, 0));
        make_root(bp);
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size_next = GET_SIZE(HDRP(NEXT_BLKP(bp)));
    size_t size_prev = GET_SIZE(FTRP(PREV_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc)
    { /* Case 1 */
        if (FLAG)
        {
            make_root(bp);
        }
        return bp;
    }

    else if (prev_alloc && !next_alloc)
    { /* Case 2 */
        disconnect(NEXT_BLKP(bp));
        size += size_next;
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc)
    {

        disconnect(PREV_BLKP(bp));
        size += size_prev;
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else
    {
        disconnect(PREV_BLKP(bp));
        disconnect(NEXT_BLKP(bp));
        size += (size_prev + size_next);
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    make_root(bp);
    return bp;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
    /* Coalesce if the previous block was free */

    return coalesce(bp);
}

int mm_init(void)
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(96)) == (void *)-1)
    {
        return -1;
    }
    heap_start = heap_listp;
    dense_start = heap_listp + WSIZE;
    root_last = heap_listp + 76;

    /*Allocate space for the seglist roots*/

    PUT(heap_listp, 0);                             /* Alignment padding */
    PUT(heap_listp + (21 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (22 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (23 * WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (22 * WSIZE);
    FLAG = 0;
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    extend_heap(16);
    PUTP(dense_start + WSIZE, heap_listp + DSIZE);
    PUTP(heap_listp + 3 * WSIZE, NULL);
    PUTP(heap_listp + DSIZE, NULL);
    FLAG = 1;
    for (int i = 0; i < 19; i++)
    {
        if (i == 1)
        {
            continue;
        }
        PUTP(dense_start + i * WSIZE, NULL);
    }

    return 0;
}
/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size == 0)
    {
        return NULL;
    }
    /* Adjust block size to include overhead and alignment reqs. */
    asize = ALIGN(size + SIZE_T_SIZE);

    if (asize < 24)
    {
        asize = 24;
    } /*the least allocation size to accomodate explicit free list feature */

    /* Search the free list for a fit */

    if (asize <= 128)
    {
        bp = dense_fit(asize);
    }
    else
    {
        bp = sparse_fit(asize);
    }

    if (bp != NULL)
    {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
    {
        return NULL;
    }
    place(bp, asize);
    return bp;
}

void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

void *mm_realloc(void *ptr, size_t size)
{
    size_t oldsize;
    void *newptr;
    size = ALIGN(size + SIZE_T_SIZE);

    if (size == 0)
    {
        mm_free(ptr);
        return 0;
    }

    if (ptr == NULL)
    {
        return mm_malloc(size);
    }
    oldsize = GET_SIZE(HDRP(ptr));

    if (size == oldsize)
    {
        return ptr;
    }

    else if (size < oldsize)
    {
        if (oldsize - size >= 64)
        {
            PUT(HDRP(ptr), PACK(size, 1));
            PUT(HDRP(ptr), PACK(size, 1));
            PUT(HDRP(NEXT_BLKP(ptr)), PACK(oldsize - size, 0));
            PUT(HDRP(NEXT_BLKP(ptr)), PACK(oldsize - size, 0));
            make_root(NEXT_BLKP(ptr));
            return ptr;
        }
        else
        {
            PUT(HDRP(ptr), PACK(oldsize, 1));
            PUT(HDRP(ptr), PACK(oldsize, 1));
            return ptr;
        }
    }
    else
    {
        size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
        size_t size_next = GET_SIZE(HDRP(NEXT_BLKP(ptr)));

        if (!next_alloc && ((oldsize + size_next) >= size))
        {
            disconnect(NEXT_BLKP(ptr));
            size_t leftover = oldsize + size_next - size;

            if (leftover >= 64)
            {
                PUT(HDRP(ptr), PACK(size, 1));
                PUT(FTRP(ptr), PACK(size, 1));
                PUT(HDRP(NEXT_BLKP(ptr)), PACK(leftover, 0));
                PUT(FTRP(NEXT_BLKP(ptr)), PACK(leftover, 0));
                make_root(NEXT_BLKP(ptr));
                return ptr;
            }
            else
            {

                PUT(HDRP(ptr), PACK(oldsize + size_next, 1));
                PUT(FTRP(ptr), PACK(oldsize + size_next, 1));
                return ptr;
            }
        }
        else
        {
            newptr = mm_malloc(size);
            memcpy(newptr, ptr, oldsize);
            mm_free(ptr);
            return newptr;
        }
    }
}
