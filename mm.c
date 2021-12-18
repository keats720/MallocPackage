
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "Keaton",
    /* First member's full name */
    "Keaton Heisterman",
    /* First member's email address */
    "keatonh@g.ucla.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

/*definitions from the textbook */
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12) 
#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define PACK(size, alloc) ((size) | (alloc))
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = val)
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
 
#define PREVF(bp) (*(char **)(bp + WSIZE))
#define NEXTF(bp) (*(char **)(bp))


static char * heap_listp = 0;


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

static void *extend_heap(size_t word);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void* bp);
static void printblock(void *bp);
static void checkheap (int verbose);
static void checkblock(void *bp);

static void addToHeap(void * bp);
static void removeFromHeap(void * bp);

static char * freeList;
static void * bigFreeList;

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
 /* create initial empty heap */
   if ((heap_listp = mem_sbrk(4*DSIZE)) == (void *) - 1)
	return (-1);
   PUT(heap_listp, 0);
   PUT(heap_listp + WSIZE, PACK(DSIZE, 1));
   PUT(heap_listp + 2*WSIZE, PACK(DSIZE, 1));
   PUT(heap_listp + 7*WSIZE, PACK(0, 1));
   heap_listp += DSIZE;

   freeList = heap_listp + DSIZE;
   PUT(HDRP(freeList), PACK(2*DSIZE, 1));
   PUT(FTRP(freeList), PACK(2*DSIZE, 1));
   NEXTF(freeList) = heap_listp + 5*WSIZE;
   PREVF(freeList) = NULL;

   if(extend_heap(CHUNKSIZE/WSIZE) == NULL)
	return(-1);
   return(0);
}

void *mm_malloc(size_t size)
{
   size_t asize;
   size_t extendsize;
   char *bp;
   if(heap_listp == 0){
	mm_init();
   }
   if(size <= 0){
	return(NULL);
   }
   if(size <= DSIZE){
	asize = 2*DSIZE;
   }
   else{
	asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);
   }
   if((bp = find_fit(asize)) != NULL){
	place(bp, asize);
	return(bp);
   }
   extendsize = MAX(asize, CHUNKSIZE);
   if((bp = extend_heap(extendsize/WSIZE)) == NULL){
	return(NULL);
   }
   place(bp, asize);
   return(bp);

}


void mm_free(void* bp)
{
    if (bp == 0)
        return;

    size_t size = GET_SIZE(HDRP(bp));

    if (heap_listp == 0) {
        mm_init();
    }


    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */

static void* coalesce(void* bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 */
	addToHeap(bp);  
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
	size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
	removeFromHeap(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
	addToHeap(bp);
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */	
	size += GET_SIZE(HDRP(PREV_BLKP(bp)));

	bp = PREV_BLKP(bp);
	removeFromHeap(bp);

	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	addToHeap(bp);
    }

    else {                                     /* Case 4 */
	size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        
	removeFromHeap(NEXT_BLKP(bp));
	removeFromHeap(PREV_BLKP(bp));
	bp = PREV_BLKP(bp);
	
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));

	addToHeap(bp);
    }

    return bp;
}


/*
 * mm_realloc - Naive implementation of realloc
 */
void* mm_realloc(void * ptr, size_t size)
{
    /* If size == 0 then this is just free, and we return NULL. */
    if (size == 0) {
        mm_free(ptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if (ptr == NULL) {
        return mm_malloc(size);
    }
	
    size_t oldSize = GET_SIZE(HDRP(ptr));
    size_t newSize;
    if (size <= DSIZE){
	newSize = 2*DSIZE;
    }
    else{
	newSize = DSIZE*((size + DSIZE + (DSIZE-1))/DSIZE);
    }
    if(newSize == oldSize){
	return(ptr);
    }
    //break into 3 possibilities
    //1 - old > new which just means use current block 
    //2 - new > old BUT prev or next block is free and if
    // added is big enough to take new size
    //3 - we need to find a completely new block
    if(oldSize > newSize){
	if((oldSize - newSize) >= 2*DSIZE){
            PUT(HDRP(ptr), PACK(newSize, 1));
            PUT(FTRP(ptr), PACK(newSize, 1));
            PUT(HDRP(NEXT_BLKP(ptr)), PACK(oldSize - newSize, 0));
            PUT(FTRP(NEXT_BLKP(ptr)), PACK(oldSize - newSize, 0));
            addToHeap(NEXT_BLKP(ptr));
	}
        return(ptr);
    }
    size_t netSize;
    if(!GET_ALLOC(NEXT_BLKP(ptr)) && ((netSize = oldSize + GET_SIZE(HDRP(NEXT_BLKP(ptr)))) >= newSize) ){
	removeFromHeap(NEXT_BLKP(ptr));
	PUT(HDRP(ptr), PACK(netSize, 1));
	PUT(FTRP(ptr), PACK(netSize, 1));
	
	//cutSize = netSize - newSize;
	//if(cutSize >= 2*DSIZE){
	    


	return(ptr);
    }
    else if(!GET_ALLOC(PREV_BLKP(ptr)) && ((netSize = oldSize + GET_SIZE(HDRP(PREV_BLKP(ptr)))) >= newSize)){
	removeFromHeap(PREV_BLKP(ptr));
	void * newBlock = PREV_BLKP(ptr);
	PUT(HDRP(newBlock), PACK(netSize, 1));
	PUT(FTRP(newBlock), PACK(netSize, 1));
	memcpy(newBlock, ptr, oldSize);
	return(newBlock);
    }
    else{
	void * newBlock = mm_malloc(newSize);
	if(newBlock == NULL)
	    return(0);
	memcpy(newBlock, ptr, oldSize);
	mm_free(ptr);
	return(newBlock);	
    }
    return(ptr);
    return(NULL);
}

/* checkheap - We don't check anything right now.
 */
void mm_checkheap(int verbose)
{
}



 /*
  * extend_heap - Extend heap with free block and return its block pointer
  */
  
static void* extend_heap(size_t words)
{
    char* bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; 
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;                                        

        /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */   //line:vm:mm:freeblockhdr
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */   //line:vm:mm:freeblockftr
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */ //line:vm:mm:newepihdr

    /* Coalesce if the previous block was free */
    return coalesce(bp);                                          //line:vm:mm:returnblock
}

/*
 * place - Place block of asize bytes at start of free block bp
 *         and split if remainder would be at least minimum block size
 */

static void place(void* bp, size_t asize)

{
    removeFromHeap(bp);

    size_t csize = GET_SIZE(HDRP(bp));
	
    if ((csize - asize) >= (2 * DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    	
	coalesce(bp);
	
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}


/*
 * find_fit - Find a fit for a block with asize bytes
 */

static void* find_fit(size_t asize)
/* $end mmfirstfit-proto */
{
    void * bp = freeList;
    while(GET_ALLOC(HDRP(bp)) != 1){
	if(asize <= GET_SIZE(HDRP(bp))){
	    return(bp);
	}
        bp = NEXTF(bp);
    }
    return NULL; /* No fit */
}

static void printblock(void* bp)
{
    size_t hsize, halloc, fsize, falloc;

    checkheap(0);
    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));

    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }

    /*  printf("%p: header: [%p:%c] footer: [%p:%c]\n", bp,
    hsize, (halloc ? 'a' : 'f'),
    fsize, (falloc ? 'a' : 'f')); */
}

static void checkblock(void* bp)
{
    if ((size_t)bp % 8)
        printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("Error: header does not match footer\n");
}

/*
 * checkheap - Minimal check of the heap for consistency
 */
void checkheap(int verbose)
{
    char* bp = heap_listp;

    if (verbose)
        printf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
        printf("Bad prologue header\n");
    checkblock(heap_listp);

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose)
            printblock(bp);
        checkblock(bp);
    }

    if (verbose)
        printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
        printf("Bad epilogue header\n");
}

static void addToHeap(void * bp){
    NEXTF(bp) = freeList;
    PREVF(bp) = NULL;
    PREVF(freeList) = bp;
    freeList = bp;
}

static void removeFromHeap(void * bp){
    if(PREVF(bp) == NULL){
	freeList = NEXTF(bp);
	PREVF(NEXTF(bp)) = NULL;
    }
    else{
	NEXTF(PREVF(bp)) = NEXTF(bp);
	PREVF(NEXTF(bp)) = PREVF(bp);
    }   
}




