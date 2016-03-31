/*
 * Simple, 32-bit and 64-bit clean allocator based on a segregated explicit free list,
 * best fit placement, and boundary tag coalescing. Blocks are aligned to double-word boundaries.
 * This yields 8-byte aligned blocks on a 32-bit processor, and 16-byte aligned
 * blocks on a 64-bit processor.  However, 16-byte alignment is stricter
 * than necessary; the assignment only requires 8-byte alignment.  The
 * minimum block size is four words.
 *
 * This allocator uses the size of a pointer, e.g., sizeof(void *), to
 * define the size of a word.  This allocator also uses the standard
 * type uintptr_t to define unsigned integers that are the same size
 * as a pointer, i.e., sizeof(uintptr_t) == sizeof(void *).
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
	/* Team name */
	"Jedi Knights",
	/* First member's full name */
	"Aaditya Thakkar",
	/* First member's email address */
	"201401009@daiict.ac.in",
	/* Second member's full name (leave blank if none) */
	"Aaska Shah",
	/* Second member's email address (leave blank if none) */
	"201401029@daiict.ac.in"
};

/* Basic constants and macros: */
#define WSIZE      sizeof(void *) /* Word and header/footer size (bytes) */
#define DSIZE      (2 * WSIZE)    /* Doubleword size (bytes) */
#define CHUNKSIZE  (1 << 12)      /* Extend heap by this amount (bytes) */

#define MAX(x, y)  ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word. */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p. */
#define GET(p)       (*(uintptr_t *)(p))
#define PUT(p, val)  (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p. */
#define GET_SIZE(p)   (GET(p) & ~(DSIZE - 1))
#define GET_ALLOC(p)  (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer. */
#define HDRP(bp)  ((char *)(bp) - WSIZE)
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks. */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Global variables: */
static char *heap_listp; /* Pointer to first block */

/* Added Global variables: */
size_t num_seg_lists = 10;
static char** heap_seg_list;

/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);

static void place(void *bp, size_t asize,bool heapExtended);

/* Function prototypes for heap consistency checker routines: */
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp);

/* Additional Function prototypes for heap consistency checker routines: */
static void checkfreeblock(void *bp);

/* Additional function prototypes */
static int get_list_id(size_t size);
static void list_add_block(void *bp);
static void list_remove_block(void *bp);
static void* coalesce_for_segregated(void *bp);
static void* segregated_best_fit(size_t asize);

/* Defining additional macros for segregated list */

//GET SEGREGATED LIST NEXT AND PREV BLOCKS
#define SEG_GET_NEXT_BLKP(bp) GET(bp)
#define SEG_GET_PREV_BLKP(bp) GET((char *)(bp)+WSIZE)

//SET SEGREGATED LIST NEXT AND PREV BLOCKS for a block with block pointer bp
#define SEG_SET_NEXT_BLKP(bp, next_block_ptr) PUT(bp, next_block_ptr)
#define SEG_SET_PREV_BLKP(bp, prev_block_ptr) PUT((char *)(bp)+WSIZE, prev_block_ptr)

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Initialize the memory manager.  Returns 0 if the memory manager was
 *   successfully initialized and -1 otherwise.
 */
int
mm_init(void)
{
    if((heap_seg_list = mem_sbrk(num_seg_lists*WSIZE)) == (void *)-1)  /*allocate space for segregated list in heap*/
		    return (-1);
	/* Create the initial empty heap. */
	if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
		return (-1);
	PUT(heap_listp, 0);                            /* Alignment padding */
	PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
	PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
	PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
	heap_listp += (2 * WSIZE);
  int i;
        for (i = 0; i < num_seg_lists; i++)
                heap_seg_list[i] = NULL;

	return (0);
}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Allocate a block with at least "size" bytes of payload, unless "size" is
 *   zero.  Returns the address of this block if the allocation was successful
 *   and NULL otherwise.
 */
void *
mm_malloc(size_t size)
{
	size_t asize;                           /* Adjusted block size */
	size_t extendsize;                      /* Amount to extend heap if no fit */
	void *bp;

	/* Ignore spurious requests. */
	if (size == 0)
		return (NULL);

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE)
		asize = 2 * DSIZE;
	else
		asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);

	/* Search the free list for a fit. */
	if ((bp = segregated_best_fit(asize)) != NULL) {
		place(bp, asize,false);
		return (bp);
	}

	/* No fit found.  Get more memory and place the block. */
	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
		return (NULL);
	place(bp, asize,true);
	return (bp);
}

/*
 * Requires:
 *   "bp" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Free a block.
 */
void
mm_free(void *bp)
{
	size_t size;

	/* Ignore spurious requests. */
	if (bp == NULL)
		return;

	/* Free and coalesce the block. */
	size = GET_SIZE(HDRP(bp));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	coalesce_for_segregated(bp);
}

/*
 * Requires:
 *   "ptr" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Reallocates the block "ptr" to a block with at least "size" bytes of
 *   payload, unless "size" is zero.  If "size" is zero, frees the block
 *   "ptr" and returns NULL.  If the block "ptr" is already a block with at
 *   least "size" bytes of payload, then "ptr" may optionally be returned.
 *   Otherwise, a new block is allocated and the contents of the old block
 *   "ptr" are copied to that new block.  Returns the address of this new
 *   block if the allocation was successful and NULL otherwise.
 */
void *
mm_realloc(void *ptr, size_t size)
{
            size_t oldsize;
	    void *newptr;

	    /* If size == 0 , free the block. */
	    if (size == 0){
		mm_free(ptr);
		return NULL;
	    }

	    /*If the realloc'd block has previously been given more size than it needs, perhaps
	       this realloc request can be serviced within the same block:*/
	    size_t curSize = GET_SIZE(HDRP(ptr));
	    if (size < curSize-2*WSIZE) {
		return ptr;
	    }

	    
	    /*If next block is not allocated, realloc request can be serviced by merging both blocks*/
	    void *next = NEXT_BLKP(ptr);
	    int next_alloc = GET_ALLOC(HDRP(next));

	    size_t coalesce_size = (GET_SIZE(HDRP(next)) + GET_SIZE(HDRP(ptr)));
	    if (!next_alloc && size <= coalesce_size-2*WSIZE){
		list_remove_block(next);
		PUT(HDRP(ptr), PACK(coalesce_size, 1));
		PUT(FTRP(ptr), PACK(coalesce_size, 1));
		return ptr;
	    }

            /* If old ptr is NULL, then this is just malloc. */
	    if (ptr == NULL)
		return (mm_malloc(size));

            newptr = mm_malloc(size);

	    /* If realloc() fails the original block is left untouched  */
	    if (newptr == NULL)
		    return (NULL);


	    /* Copy the old data. */
	    oldsize = GET_SIZE(HDRP(ptr));
	    if (size < oldsize)
	            oldsize = size;
	    memcpy(newptr, ptr, oldsize);

	    /* Free the old block. */
	    mm_free(ptr);

	    return (newptr);
}

/*
 * The following routines are internal helper routines.
 */

/*
 * Requires:
 *   "bp" is the address of a newly freed block.
 *
 * Effects:
 *   Perform boundary tag coalescing.  Returns the address of the coalesced
 *   block.
 */
static void *
coalesce(void *bp)
{
	bool prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	bool next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));

	if (prev_alloc && next_alloc) {                 /* Case 1 : previous and next allocated*/
		return (bp);
	} else if (prev_alloc && !next_alloc) {         /* Case 2 : next block free*/
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
	} else if (!prev_alloc && next_alloc) {         /* Case 3 : previous block free */
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	} else {                                        /* Case 4 : both next and previous blocks free*/
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
		    GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}
        return bp;
}


/*
 * Requires:
 *   `bp` is the address of a newly freed block
 *
 * Effects:
 *    Perform boundary tag coalescing.  Returns the address of the coalesced
 *    block.
 */
static void *
coalesce_for_segregated(void *bp)
{
        if (GET_ALLOC(FTRP(PREV_BLKP(bp))) && GET_ALLOC(HDRP(NEXT_BLKP(bp)))) {    /* Case 1 : previous and next allocated*/
            list_add_block(bp);							   /* directly add to free list */
        }

        if (GET_ALLOC(FTRP(PREV_BLKP(bp))) && !GET_ALLOC(HDRP(NEXT_BLKP(bp)))) {    /* Case 2 : next block free*/
            void *next = NEXT_BLKP(bp);
            list_remove_block(next);
            bp = coalesce(bp);
            list_add_block(bp);
        }

        if (!GET_ALLOC(FTRP(PREV_BLKP(bp))) && GET_ALLOC(HDRP(NEXT_BLKP(bp)))) {    /* Case 3 : previous block free */
            void *prev = PREV_BLKP(bp);
            list_remove_block(prev);
            bp = coalesce(bp);
            list_add_block(bp);
        }

        if (!GET_ALLOC(FTRP(PREV_BLKP(bp))) && !GET_ALLOC(HDRP(NEXT_BLKP(bp)))) {    /* Case 4 : both next and previous blocks free*/
            void *prev = PREV_BLKP(bp);
            void *next = NEXT_BLKP(bp);
            list_remove_block(prev);
            list_remove_block(next);
            bp = coalesce(bp);
            list_add_block(bp);
        }
        return bp;
}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Extend the heap with a free block and return that block's address.
 */
static void *
extend_heap(size_t words)
{
	void *bp;
	size_t size;

	/* Allocate an even number of words to maintain alignment. */
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	if ((bp = mem_sbrk(size)) == (void *)-1)
		return (NULL);

	/* Initialize free block header/footer and the epilogue header. */
	PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
	PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

	return bp;
}

/*
 * Requires:
 *   "bp" is the address of a free block that is at least "asize" bytes.
 *
 * Effects:
 *   Place a block of "asize" bytes at the start of the free block "bp" and
 *   split that block if the remainder would be at least the minimum block
 *   size.
 */
static void
place(void *bp, size_t asize, bool heapExtended)
{
	/* Get the current block size */
	size_t csize = GET_SIZE(HDRP(bp));

        if (heapExtended == true) {                        /*when heap is extended*/
		if ((csize - asize) >= (2 * DSIZE)) {		/*if block size is greater than the asize, splicing takes place */
			PUT(HDRP(bp), PACK(asize, 1));
			PUT(FTRP(bp), PACK(asize, 1));
			/*splice block*/
			bp = NEXT_BLKP(bp);
			PUT(HDRP(bp), PACK(csize - asize, 0));
			PUT(FTRP(bp), PACK(csize - asize, 0));
			/*Put the newly spliced free block at front of the free list*/
                        list_add_block(bp);
		} else {					/*else no splicing necessary, they are getting the whole block*/
			PUT(HDRP(bp), PACK(csize, 1));
			PUT(FTRP(bp), PACK(csize, 1));
		}
        }
        else {
                if ((csize - asize) >= (2 * DSIZE)) {		/*if block size is greater than the asize, splicing takes place */
                        list_remove_block(bp);
			PUT(HDRP(bp), PACK(asize, 1));
			PUT(FTRP(bp), PACK(asize, 1));
			/*splice block*/
			bp = NEXT_BLKP(bp);
			PUT(HDRP(bp), PACK(csize - asize, 0));
			PUT(FTRP(bp), PACK(csize - asize, 0));
			/*Put the newly spliced free block at front of the free list*/
                        list_add_block(bp);
		} else {					/*else no splicing necessary, they are getting the whole block*/
			PUT(HDRP(bp), PACK(csize, 1));
			PUT(FTRP(bp), PACK(csize, 1));
                        list_remove_block(bp);
		}
        }
}
/*
 * Requires:
 *   none.
 *
 * Effects:
 *   Gives an index of the list from an array.
 */
static int
get_list_id(size_t size)
{
        if (size > 16384)
            return 9;
        else if (size > 8192)
            return 8;
        else if (size > 4096)
            return 7;
        else if (size > 2048)
            return 6;
        else if (size > 1024)
            return 5;
        else if (size > 512)
            return 4;
        else if (size > 256)
            return 3;
        else if (size > 128)
            return 2;
        else if (size > 64)
            return 1;
        else
            return 0;

}
/*
 * Requires:
 *   `bp` is the address of a newly freed block (or a bigger sized block retrieved while coalescing)
 *
 * Effects:
 *    Adding block pointer `bp` to the segregated list of appropriate size.
 */
static void
list_add_block(void *bp)
{
        int id = get_list_id(GET_SIZE(HDRP(bp)));     /*select appropriate list in which block needs to be added*/

        SEG_SET_NEXT_BLKP(bp, heap_seg_list[id]);     /*insert at the start of the list*/
        SEG_SET_PREV_BLKP(bp, NULL);

        if (heap_seg_list[id] != NULL)
                 SEG_SET_PREV_BLKP(heap_seg_list[id], bp);
        heap_seg_list[id] = bp;
        return;
}

/*
 * Requires:
 *   `bp` is the address of a newly Allocated block (or a smaller sized block used in coalescing)
 *
 * Effects:
 *    Removing block pointer`bp` from the segregated list of appropriate size.
 */
static void
list_remove_block(void *bp)    
{

        int id = get_list_id(GET_SIZE(HDRP(bp)));   /*select appropriate list from which block needs to be removed*/

        if (SEG_GET_PREV_BLKP(bp) != NULL)
                SEG_SET_NEXT_BLKP(SEG_GET_PREV_BLKP(bp),SEG_GET_NEXT_BLKP(bp));
        else
                heap_seg_list[id] = SEG_GET_NEXT_BLKP(bp);

        if (SEG_GET_NEXT_BLKP(bp) != NULL)
                SEG_SET_PREV_BLKP(SEG_GET_NEXT_BLKP(bp), SEG_GET_PREV_BLKP(bp));
        return;
}


/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Find a fit for a block with "asize" bytes.  Returns that block's address
 *   or NULL if no suitable block was found.
 */
static void *
segregated_best_fit(size_t asize)
{
        size_t min_diff = 9999999;
        void *bestfit = NULL;
        int i;
        int id = get_list_id(asize);
        for (i = id; i < num_seg_lists; i++) {      /* start searching from the list whose block size is just greater than or equal asize */
                void *bp = heap_seg_list[i];
                while (bp) {                               /*go through the linked list*/
                        size_t curr_size = GET_SIZE(HDRP(bp));
                        if (!GET_ALLOC(HDRP(bp)) && (asize <= curr_size)) {
                                size_t diff = curr_size;
                                if (diff < min_diff) {		/*find best fit from the list*/
                                        min_diff = diff;
                                        bestfit = bp;
                                }

                        }
                        bp  = SEG_GET_NEXT_BLKP(bp);
                }

                if(bestfit!= NULL)		/*if we get a fit in the list, no need to check other lists of higher sizes.*/
                       return bestfit;
        }
        return bestfit;
}

/*
 * The remaining routines are heap consistency checker routines.
 */

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Perform a minimal check on the block "bp".
 */
static void
checkblock(void *bp)
{
	size_t alloc, prev_alloc, next_alloc;
	alloc = GET_ALLOC(HDRP(bp));
	prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

	if ((uintptr_t)bp % DSIZE)               /* checks if block is double word aligned*/
		printf("Error: %p is not doubleword aligned\n", bp);

	if (GET(HDRP(bp)) != GET(FTRP(bp)))      /*checks if header matches footer*/
		printf("Error: header does not match footer\n");

	if((!alloc) && !(prev_alloc & next_alloc)){   /*checks if contiguous free blocks somehow escaped coalescing*/
		printf("%p consecutive free blocks\n", bp);
		exit(-1);
	}
}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Perform a minimal check of the heap for consistency.
 */

void
checkheap(bool verbose)
{
	void *bp;
	int numfreeblocks_heap = 0;
	int numfreeblocks_list = 0;
	if (verbose)
		printf("Heap (%p):\n", heap_listp);

	if (GET_SIZE(HDRP(heap_listp)) != DSIZE || !GET_ALLOC(HDRP(heap_listp)))   /*checks Prologue header*/
		printf("Bad prologue header\n");
	checkblock(heap_listp);

	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {  /*checks each block */
		if (verbose)
			printblock(bp);
		checkblock(bp);
		if(!GET_ALLOC(HDRP(bp)))               /* counts the total number of free blocks in the heap */
			numfreeblocks_heap++;
	}

	if (verbose)
		printblock(bp);
	if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp)))
		printf("Bad epilogue header\n");

	/* Free list checking */
	int i = 0;
	for(i = 0; i < num_seg_lists; i++)
	{
		if(heap_seg_list[i]!=NULL){
			for(bp = heap_seg_list[i]; bp!=NULL && GET_ALLOC(HDRP(bp)) == 0; bp = SEG_GET_NEXT_BLKP(bp))
			{
				checkfreeblock(bp);
				numfreeblocks_list++;
			}
		}
	}

	/* Check if number of free blocks in the heap and segregated list match */
	if(numfreeblocks_list != numfreeblocks_heap)
	{
		printf("Mismatch between free blocks in heap and free list\n");
		exit(-1);
	}
}

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Perform a minimal check on the free block "bp".
 */
static void
checkfreeblock(void *bp)
{
 /*Checks if the pointers in the free list point to valid free blocks*/

	if(SEG_GET_PREV_BLKP(bp))   /*has a previous block*/
	{
		if(SEG_GET_NEXT_BLKP(SEG_GET_PREV_BLKP(bp)) != bp)  /*the next of previous block should point to the current block*/
		{
			printf("Free list inconsistent at %p\n", bp);
			exit(-1);
		}
	}

	if(SEG_GET_NEXT_BLKP(bp) && SEG_GET_NEXT_BLKP(bp) != heap_listp)
	{
		if(SEG_GET_PREV_BLKP(SEG_GET_NEXT_BLKP(bp)) != bp)  /*the previous of next block should point to the current block*/
		{
			printf("Free list inconstitent at %p\n", bp);
			exit(-1);
		}
	}

}

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Print the block "bp".
 */
static void
printblock(void *bp)
{
	bool halloc, falloc;
	size_t hsize, fsize;

	checkheap(false);
	hsize = GET_SIZE(HDRP(bp));    
	halloc = GET_ALLOC(HDRP(bp));
	fsize = GET_SIZE(FTRP(bp));
	falloc = GET_ALLOC(FTRP(bp));

	if (hsize == 0) {
		printf("%p: end of heap\n", bp);
		return;
	}

	printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp,
	    hsize, (halloc ? 'a' : 'f'),
	    fsize, (falloc ? 'a' : 'f'));
}

/*
 * The last lines of this file configures the behavior of the "Tab" key in
 * emacs.  Emacs has a rudimentary understanding of C syntax and style.  In
 * particular, depressing the "Tab" key once at the start of a new line will
 * insert as many tabs and/or spaces as are needed for proper indentation.
 */

/* Local Variables: */
/* mode: c */
/* c-default-style: "bsd" */
/* c-basic-offset: 8 */
/* c-continued-statement-offset: 4 */
/* indent-tabs-mode: t */
/* End: */
