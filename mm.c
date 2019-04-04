/* 
 * Simple, 32-bit and 64-bit clean allocator based on an implicit free list,
 * first fit placement, and boundary tag coalescing, as described in the
 * CS:APP3e text.  Blocks are aligned to double-word boundaries.  This
 * yields 8-byte aligned blocks on a 32-bit processor, and 16-byte aligned
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
	" KeBo",
	/* First member's full name */
	" Bowen Liu",
	/* First member's NetID */
	" bl28 ",
	/* Second member's full name (leave blank if none) */
	" Tianrun Ke",
	/* Second member's NetID (leave blank if none) */
	" tk26"
};

/* Basic constants and macros: */
#define WSIZE      sizeof(void *) /* Word and header/footer size (bytes) */
#define DSIZE      (2 * WSIZE)    /* Doubleword size (bytes) */
#define CHUNKSIZE  4112      /* Extend heap by this amount (bytes) */
// #define COALESCE_THRESHOLD  8223

#define MAX(x, y)  ((x) > (y) ? (x) : (y))  
#define MIN(x, y)  ((x) < (y) ? (x) : (y)) 

/* Pack a size and allocated bit into a word. */
#define PACK(size, prev_alloc, alloc)  ((size) | (alloc) | (prev_alloc << 1))

/* Read and write a word at address p. */
#define GET(p)       (*(uintptr_t *)(p))
#define PUT(p, val)  (*(uintptr_t *)(p) = (val))

/* Read and write prev pointer*/
#define GET_PREV(p)       (GET((char *)(p) + WSIZE))
#define PUT_PREV(p, val)  (PUT(((char *)(p) + WSIZE),val))

/* Read and write next pointer*/
#define GET_NEXT(p)       (GET((char *)(p) + DSIZE))
#define PUT_NEXT(p, val)  (PUT(((char *)(p) + DSIZE),val))
#define TO_FTRP(p)	  ((char *)p + GET_SIZE(p) - WSIZE)
#define TO_BLKP(p)	  ((char *)p + 3 * WSIZE)



/* Read the size and allocated fields from address p. */
#define GET_SIZE(p)      (GET(p) & ~(DSIZE - 1))
#define GET_ALLOC(p)  	 (GET(p) & 0x1)
#define GET_PRE_ALLOC(p) ((GET(p) & 0x2) >> 1)
#define GET_NEXT_ALLOC(p)	(GET_ALLOC(NEXT_H(p)))

#define NEXT_H(p)	  ((char *)(p) + GET_SIZE(p))
#define PREV_H(p)	  ((char *)(p) - GET_SIZE(p - WSIZE))

/* Given block ptr bp, compute address of its header and footer. */
#define HDRP(bp)   ((char *)(bp) - 3 * WSIZE)
#define FTRP(bp)   ((char *)(bp) + GET_SIZE(HDRP(bp)) - 2 * DSIZE)
#define PREV_P(bp) (HDRP(bp) + WSIZE)
#define NEXT_P(bp) (PREV_P(bp) + WSIZE)

/* Given block ptr bp, compute address of next and previous blocks. */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(HDRP(bp) - WSIZE))

#define SEGLISTCOUNT 19
/* Global variables: */
static char *heap_listp; /* Pointer to first block */  

/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *re_extend_heap(size_t words);
static void *find_fit(size_t asize);
static void *place(void *bp, size_t asize);

/* Function prototypes for heap consistency checker routines: */
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp); 
void insert_free_block(void* p);
void remove_free_block(void* p, int index);
int get_list_index(size_t size);
size_t get_size(size_t size);


static uintptr_t **freelists;

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

	/* Create the initial empty heap. */

	if ((heap_listp = mem_sbrk(24 * WSIZE)) == (void *)-1)
		return (-1);
	PUT(heap_listp, 0);
	freelists = (uintptr_t **)(heap_listp + WSIZE);                            /* Alignment padding */
	PUT(heap_listp + (21 * WSIZE), PACK(DSIZE, 0, 1)); /* Prologue header */ 
	PUT(heap_listp + (22 * WSIZE), PACK(DSIZE, 0, 1)); /* Prologue footer */ 
	PUT(heap_listp + (23 * WSIZE), PACK(0, 0, 1));     /* Epilogue header */
	heap_listp += (23 * WSIZE);

	/* Initialize the freelists to be NULL */
	memset((void *)freelists, 0, SEGLISTCOUNT * WSIZE);

	/* Extend the empty heap with a free block of CHUNKSIZE bytes. */
	if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
		return (-1);
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

	size_t asize;      /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if no fit */
	void *bp;

	/* Ignore spurious requests. */
	if (size == 0)
		return (NULL);

	/* Adjust block size to include overhead and alignment reqs. */
	asize = get_size(size);

	/* Search the free list for a fit. */
	if ((bp = find_fit(asize)) != NULL) {
		return (bp - DSIZE);
	}

	/* No fit found.  Get more memory and place the block. */
	extendsize = MAX(asize , CHUNKSIZE);
	if ((bp = re_extend_heap(extendsize)) == NULL)
	{
		return (NULL);
	}  

	
	void* header = place(HDRP(bp), asize);
	/* Return the allocated block's payload pointer*/
	return (header + WSIZE);
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

	/* Convert to free block's payload pointer*/
	bp = bp + DSIZE;

	/* Free and coalesce the block. */
	size = GET_SIZE(HDRP(bp));
	int prev_alloc = GET_PRE_ALLOC(HDRP(bp));
	PUT(HDRP(bp), PACK(size, prev_alloc, 0));
	PUT(FTRP(bp), PACK(size, prev_alloc, 0));

	/* coalesce the block if it is very small/large or equal Chunksize*/
	if(size <= 9 * DSIZE || size == CHUNKSIZE 
		||size > 1527 * DSIZE|| (size >= 625 * DSIZE && size <= 844 * DSIZE) )
		bp = coalesce(bp);

	insert_free_block(HDRP(bp));
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
void *mm_realloc(void *ptr, size_t size)
{

	/* free the block. */
	if(size == 0 )
	{
		mm_free(ptr);
		return NULL;
	}

	/* just allocate a new block */
	if(ptr == NULL)
		return mm_malloc(size);


	void *newptr = ptr;
	void *header = ptr - WSIZE;
	size_t current_size = GET_SIZE(header);
	void *next_header; 
	void *prev_header;
	size_t asize; /* Adjusted block size */


	/* Adjust block size to include overhead and alignment reqs. */
	asize = get_size(size);

	/* Check whether required size is greater than current block size. 
	    else do nothing. */
	if(asize > current_size)
	{
		next_header = NEXT_H(header);
		prev_header = PREV_H(header);
		size_t next_size = GET_SIZE(next_header);
		size_t prev_size = GET_SIZE(prev_header);
		
		if(GET_ALLOC(next_header)==0 && next_size + current_size >= asize)
		{

			/* if merge next free alignmented block is enough,
			   remove the free block from free lists,
			   merge the block and change flags.*/
			remove_free_block(next_header, get_list_index(next_size));
			int prev_alloc = GET_PRE_ALLOC(header);
			PUT(header, PACK(next_size + current_size, prev_alloc, 1));
			uintptr_t value = GET(NEXT_H(header));
			PUT(NEXT_H(header),value | 0x2);			

		}
		else if(GET_PRE_ALLOC(header)==0 && prev_size + current_size >= asize)
		{
			/* if merge prev free alignmented block is enough,
			   remove the free block from free lists,
			   merge the block and change flags.*/			
			remove_free_block(prev_header, get_list_index(prev_size));
			int prev_alloc = GET_PRE_ALLOC(prev_header);
			PUT(prev_header, PACK(prev_size + current_size, prev_alloc, 1));
			memmove(prev_header + WSIZE, ptr, MIN(size, current_size  - WSIZE));
			newptr = (prev_header + WSIZE);
		}
		else if(GET_ALLOC(next_header)==0 && GET_PRE_ALLOC(header)==0 
			&& next_size + current_size + prev_size >= asize)
		{
			/* if merge next and prev free alignmented block 
			   is enough, remove the free block from free lists,
			   merge the block and change flags.*/			
			remove_free_block(prev_header, get_list_index(prev_size));
			remove_free_block(next_header, get_list_index(next_size));
			int prev_alloc = GET_PRE_ALLOC(prev_header);
			PUT(prev_header, PACK(prev_size + current_size + next_size, prev_alloc, 1));
			uintptr_t value = GET(NEXT_H(header));
			PUT(NEXT_H(header),value | 0x2);
			memmove(prev_header + WSIZE, ptr, MIN(size, current_size  - WSIZE));
			newptr = (prev_header + WSIZE);
		}
		else
		{
			// malloc a new block and copy the data
			newptr = mm_malloc(size);
			memcpy(newptr, ptr, MIN(size, current_size - WSIZE));
			mm_free(ptr);
		}
	}

	//return the reallocation block
	return newptr;
}

/*
 * The following routines are internal helper routines.
 */


/*
 * Requires: 
 * 	size is the size read from block headers
 * 
 * Effects:
 * 	Return the index of freelist according to the size
 *  
*/
int
get_list_index(size_t size)
{   
	/* Return index for round-up size*/
    	if (size < (65 * DSIZE)) {
        	switch (size)
        	{
            		case 2 * DSIZE:
                	return 0;

            	case 3 * DSIZE:
                	return 1;
            
            	case 5 * DSIZE:
                	return 2;
            
           	case 9 * DSIZE:
                	return 3;
            
            	case 17 * DSIZE:
                	return 4;
            
            	case 33 * DSIZE:
                	return 5;
            
            	default:
                	return 6;
        	}
    	}

	/* Return index for size > 2^10 bytes*/
    	else if (size <= 129 * DSIZE)
        	return 7;
    	else if (size <= 252 * DSIZE)
        	return 8;
    	else if (size <= 256 * DSIZE)
        	return 9;
    	else if (size <= 257 * DSIZE)
        	return 10;
    	else if (size <= 513 * DSIZE)
        	return 11;
    	else if (size <= 769 * DSIZE)
        	return 12;
    	else if (size <= 1015 * DSIZE)
        	return 13;
    	else if (size <= 1271 * DSIZE)
        	return 14;
    	else if (size <= 1527 * DSIZE)
        	return 15;
    	else if (size <= 1783 * DSIZE)
        	return 16;
    	else if (size <= 2039 * DSIZE)
        	return 17;

	
    	return 18;

}



/*
 * Requires:
 * 	size is number of bytes of payload to be allocated 
 * Effects:
 * 	 Convert the payload size to block size
*/
size_t get_size(size_t size)
{
	/* If size smaller than 2^10 round up the size to nearest power of 2*/
	if (size <= 3 * WSIZE)
		return 2 * DSIZE;
	if (size <= 5 * WSIZE)
		return 3 * DSIZE;
	if (size <= 9 * WSIZE)
		return 5 * DSIZE;
	if (size <= 17 * WSIZE)
		return 9 * DSIZE;
	if (size <= 33 * WSIZE)
		return 17 * DSIZE;
	if (size <= 65 * WSIZE)
		return 33 * DSIZE;
	if (size < 129 * WSIZE)
		return 65 * DSIZE;

	/* directly convert the size */
	return (DSIZE * ((size + WSIZE + (DSIZE - 1)) / DSIZE));
	
}


/*
 * Requires:
 *   "bp" is the address of a newly freed block.
 *
 * Effects:
 *   Perform boundary tag coalescing.  Returns the address of the coalesced
 *   block.
 */
static void*
coalesce(void *bp) 
{
    	int prev_alloc = GET_PRE_ALLOC(HDRP(bp));
    	int next_alloc = GET_NEXT_ALLOC(HDRP(bp));
	
	
	if ((prev_alloc == 1) && (next_alloc == 1)) {  

		/* no free block to merge. */
		uintptr_t next_header = GET(HDRP(NEXT_BLKP(bp)));
		
		// update next block' prev_alloc flag
		PUT(HDRP(NEXT_BLKP(bp)), next_header & ~0x2);

	} else if ((prev_alloc == 1) && (next_alloc == 0)) {        

        	/* coalesce with next block. */

		// only coalesce large blocks
		if(GET_SIZE(NEXT_H(HDRP(bp))) <= 17 * DSIZE)
			return (bp);
		void* next_header = HDRP(NEXT_BLKP(bp));
		size_t next_size = GET_SIZE(next_header);
		int next_index = get_list_index(next_size);

		void* header = HDRP(bp);
		size_t size = GET_SIZE(HDRP(bp));

		size += next_size;

		// remove merged free blocks from free lists		
        	remove_free_block(next_header, next_index);

		// update the merged block's header and footer.		
		PUT(header, PACK(size, 1, 0));
		PUT(FTRP(bp), PACK(size, 1, 0));
	} else if ((prev_alloc == 0) && (next_alloc == 1)) {     

      		/* coalesce with previous block */

		// only coalesce large blocks
		if (GET_SIZE(PREV_H(HDRP(bp))) <= 17 * DSIZE)
			return(bp);
		void* prev_header = HDRP(PREV_BLKP(bp));
		size_t prev_size = GET_SIZE(prev_header);
		int prev_index = get_list_index(prev_size);

		size_t size = GET_SIZE(HDRP(bp));
		size += prev_size;

		// remove merged free blocks from free lists				
        	remove_free_block(prev_header, prev_index);

		// update the merged block's header and footer.
		PUT(FTRP(bp), PACK(size, 1, 0));
		PUT(prev_header, PACK(size, 1, 0));
		bp = PREV_BLKP(bp);

		// update the next alligment block's prev_alloc flag.
		uintptr_t next_header = GET(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(NEXT_BLKP(bp)), next_header & ~0x2);

	} else {                             

		// only coalesce large blocks
		if (GET_SIZE(PREV_H(HDRP(bp))) <= 17 * DSIZE
		 && GET_SIZE(NEXT_H(HDRP(bp))) <= 17 * DSIZE) {
			 return (bp);
		}

		/* coalesce with prev and next free blocks*/                                   		
		void* next_header = HDRP(NEXT_BLKP(bp));
		size_t next_size = GET_SIZE(next_header);
		int next_index = get_list_index(next_size);
		
		void* prev_header = HDRP(PREV_BLKP(bp));
		size_t prev_size = GET_SIZE(prev_header);
		int prev_index = get_list_index(prev_size);



		size_t size = GET_SIZE(HDRP(bp));
		size += (prev_size + next_size);

		// remove merged free blocks from free lists
        	remove_free_block(next_header, next_index);   
        	remove_free_block(prev_header, prev_index);

		// update the merged block's header and footer.
		PUT(prev_header, PACK(size, 1, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 1, 0));
		bp = PREV_BLKP(bp);
	}
	return(bp);
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
	size_t size;
	void *start;

	/* Allocate an even number of words to maintain alignment. */
	if (words <= 4)
		size = 2 * DSIZE;
	else
	{
		size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	}

	
	
	if ((start = mem_sbrk(size)) == (void *)-1)  
		return (NULL);

	/* Initialize free block header/footer and the epilogue header. */
	PUT(start - WSIZE, PACK(size, 1, 0));         /* Free block header */
	PUT(FTRP(start + DSIZE), PACK(size, 0, 0));         /* Free block footer */
	PUT(start + size - WSIZE, PACK(0, 0, 1)); /* New epilogue header */
	insert_free_block(start - WSIZE); 


	/* Coalesce if the previous block was free. */
	return (start + DSIZE);
}


/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Re-extend the heap with a free block and return that block's address
 *   and write the prev-alloc flags from the previous epilogue to new 
 *   free blocks.
 */
static void *
re_extend_heap(size_t size) 
{


	void *start;

	if ((start = mem_sbrk(size)) == (void *)-1)  
		return (NULL);


	/* Initialize free block header/footer, the epilogue header 
	   and inherit the flags. */
	PUT(start - WSIZE, PACK(size, GET_PRE_ALLOC(start - WSIZE), 0));      
	PUT(FTRP(start + DSIZE), PACK(size, GET_PRE_ALLOC(start - WSIZE), 0));      
	PUT(start + size - WSIZE, PACK(0, 0, 1)); /* New epilogue header */

	// convert to free block payload pointer, coalesce and insert it 
	void* bp = start + DSIZE;
	bp = coalesce(bp);
	insert_free_block(HDRP(bp));


	return (bp);
}




/*
 * Requires: 
 *  p is a valid free block pointer 
 *  index is a valid free list index
 * Effects:
 *  remove the p from the freelist[index] 
*/
void
remove_free_block(void* p, int index)
{

	uintptr_t prev = GET_PREV(p);
	uintptr_t next = GET_NEXT(p);

	/* if only one block in the list, empty the list*/
	if((void*) prev == p)
	{	
		freelists[index] = NULL;
		return;
	}	

	/* if remove the first one, let the list 
	   pointer be the second block pointer*/
	if(p == freelists[index])
		freelists[index] = (void*)next;

	/* remove the block*/
	PUT_NEXT(prev, next);
	PUT_PREV(next, prev);
}

/*
 * Requires: 
 *  p is a valid free block pointer 
 *  index is a valid free list index
 * Effects:
 *  insert the p into the freelist[index] 
*/
void
insert_free_block(void* p)
{

	int index = get_list_index(GET_SIZE(p));
	void* location = freelists[index];

	/* if the list is empty, let the list pointer be p*/
	if(location == NULL)
	{
		freelists[index] = p;
		PUT_PREV(p, (uintptr_t)p);
		PUT_NEXT(p, (uintptr_t)p);
		return;
	}

	/* insert the block in the end */
	uintptr_t last = GET_PREV(location);
	PUT_PREV(p, last);
	PUT_NEXT(p, (uintptr_t)location);
	PUT_NEXT(last, (uintptr_t)p);
	PUT_PREV(location, (uintptr_t)p);
}

/* 
 * Requires:
 *   "p" is the address of a free block that is at least "asize" bytes.
 *
 * Effects:
 *   Place a block of "asize" bytes at the front or back of the free block
 *   "bp" and split that block if the remainder would be at least the
 *   minimum block size. 
 */
static void*
place(void *p, size_t asize)
{
	

	void* header = p;
	void* next;
	size_t csize = GET_SIZE(header);
	remove_free_block(header, get_list_index(csize));
	int prev_alloc = GET_PRE_ALLOC(header);	

	/* if the new size is small and remain size is enough, 
	   place in the front*/
	if ( (asize < 33 * DSIZE)  && (csize - asize) >= (9 * DSIZE)) {
	
		PUT(header, PACK(csize - asize, prev_alloc,0));
		PUT(TO_FTRP(header), PACK(csize - asize, prev_alloc, 0));
		insert_free_block(header);
		header = NEXT_H(header);
		PUT(header, PACK(asize, 0, 1));
		void* next = NEXT_H(header);
		uintptr_t value = GET(next) | 0x2;
		PUT(next, value);
		return(header);
	}

	/* if the new size is big and remain size is enough, 
	   place in the back*/
	else if ((csize - asize) >= (9 * DSIZE)) {

		PUT(header, PACK(asize, prev_alloc,1));
		next = NEXT_H(header);
		PUT(next, PACK(csize - asize, 1, 0));
		PUT(TO_FTRP(next), PACK(csize - asize, 1, 0));
		insert_free_block(next);
		return(header);

	} 

	/* remain size is not enough, do not place*/
	else 
	{
		PUT(header, PACK(csize, prev_alloc, 1));
		next = NEXT_H(header);
		uintptr_t value = GET(next) | 0x2;
		PUT(next, value);
		return(p);
	}
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
find_fit(size_t asize)
{

	int index = get_list_index(asize);
	void *p = freelists[index];

	/* check the best fit list first*/
	if(p != NULL)
	{
		
		/* if the size is fit, place the block and return
		   the payload pointer*/
		if(asize <= GET_SIZE(p))
		{

			p = place(p, asize);
			return TO_BLKP(p);
		}
			

		p = (void*)GET_NEXT(p);
		while( p != freelists[index])
		{
			if (!GET_ALLOC(p) && asize <= GET_SIZE(p))
			{
				p = place(p, asize);
				return (TO_BLKP(p));
			}
			p = (void*)GET_NEXT(p);
		}
	}

	index ++;

	/* Search in the rest free lists */
	for (;index < SEGLISTCOUNT; index ++) 
	{

		/* if the size is fit, place the block and return
		   the payload pointer*/	
		void *p = freelists[index];
		if(p == NULL)
			continue;
		if(asize <= GET_SIZE(p))
		{

			p = place(p, asize);
			return TO_BLKP(p);
		}

		p = (void*)GET_NEXT(p);
		while( p != freelists[index])
		{
			if (!GET_ALLOC(p) && asize <= GET_SIZE(p))
			{
				p = place(p, asize);
				return (TO_BLKP(p));
			}

			p = (void*)GET_NEXT(p);
		}	
	}

	/* No fit was found. */
	return (NULL);
}



/* 
 * The remaining routines are heap consistency checker routines. 
 */

/*
 * Requires:
 *   "bp" is the address of the payload pointer of the free block structure
 *   which meas header plus 2 wordsize.
 *
 * Effects:
 *   Perform a minimal check on the block "bp".
 */
static void
checkblock(void *p) 
{

	if ((uintptr_t)TO_BLKP(p) % DSIZE)
		printf("Error: %p is not doubleword aligned\n", TO_BLKP(p));
	
	// check the allocated bit's consistency.
	if(GET_ALLOC(p) != GET_PRE_ALLOC(NEXT_H(p)))
		printf("Error: allocated flag doesn't match next block\n");
	if(GET_PRE_ALLOC(p) != GET_ALLOC(PREV_H(p)))
		printf("Error: allocated flag doesn't match prev block\n");

	// only check the footer when the block is free
	if (!GET_ALLOC(p))
	{
		if (GET(p) != GET(TO_FTRP(p)))
			printf("Error: header does not match footer\n");
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
	// not in debug mode, return.
	if (!verbose)
		return;

	// block's header pointer
	void *p;

	printf("The fisrt block's header address (%p):\n", heap_listp);

	// check the prologue contents
	if (GET_SIZE((heap_listp - 2 * WSIZE)) != DSIZE ||
	    !GET_ALLOC(heap_listp - 2 * WSIZE) || GET_PRE_ALLOC(heap_listp - 2 * WSIZE))
		printf("Bad prologue header\n");

	// check every block in the heap
	for (p = heap_listp; GET_SIZE(p) > 0; p = NEXT_H(p)) {
		if (verbose)
			printblock(p);
		checkblock(TO_BLKP(p));
	}

	// check the epilouge and its consistency
	printblock(p);
	if (GET_SIZE(p) != 0 || !GET_ALLOC(p))
		printf("Bad epilogue header\n");
	if (GET_ALLOC(PREV_H(p)) != GET_PRE_ALLOC(p))
		printf("Epilogue's prev alloc bit is not consistent\n");
}

/*
 * Requires:
 *   "p" is the address of a block header.
 *
 * Effects:
 *   Print the block p's size, flags, start address and end address.
 */
static void
printblock(void *p) 
{
	// avoid function non use error
	checkheap(false);

	// get the informaiton
	size_t size;
	int alloc, palloc;
	uintptr_t end_address;
	size = GET_SIZE(p);
	alloc = GET_ALLOC(p); 
	palloc = GET_PRE_ALLOC(p);
	end_address = (uintptr_t)(p + size);


	printf("the start address is: %lu; the end address is: %lu.", (uintptr_t)p, end_address); 
	printf("the block size is: %zu\n", size);
	printf("the alloc flag is: %d\n", alloc);
	printf("the prev alloc flag is: %d\n", palloc);
}
