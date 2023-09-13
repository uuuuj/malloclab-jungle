/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

// static char *root = NULL;
/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};


#define ALIGNMENT 16
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 12)
#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define PACK(size, alloc) ((size) | (alloc))
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

/*explicit 매크로*/
#define PREV(bp) (*(void**)(bp))
#define SUCC(bp) (*(void**)(bp + WSIZE))
#define SEGREGATED_SIZE (20)                                                 // 배열 사이즈 12
#define ROOT(class) (*(void **)((char *)(heap_listp) + (WSIZE * class))) // GET_ROOT(1)을 하면 1번인덱스의 루트를 얻어냄.

//function*/
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void *coalesce(void *bp);

//segregated function
static void insert_seglist(void *bp);
static void delete_seglist(void *bp);
static void *extend_heap(size_t words);
int find_position(size_t val);
static char *heap_listp;

static void insert_seglist(void *bp){
    int class = find_position(GET_SIZE(HDRP(bp)));
    SUCC(bp) = ROOT(class);
    if (ROOT(class) != NULL){
        PREV(ROOT(class)) = bp;
    }
    ROOT(class) = bp;
}
static void delete_seglist(void *bp){
    int class = find_position(GET_SIZE(HDRP(bp)));
    if (bp == ROOT(class)){
        ROOT(class) = SUCC(ROOT(class));
        return;
    }
    SUCC(PREV(bp)) = SUCC(bp);
    if(SUCC(bp) != NULL){
        PREV(SUCC(bp)) = PREV(bp);
    }
}
int find_position(size_t val){
    if(val == 0){
        return -1;
    }
    int tmp = 31-__builtin_clz(val);
    if (tmp > SEGREGATED_SIZE-1)
    {
        return SEGREGATED_SIZE - 1;
    }
    else{
        return tmp;
    }
}
//explicit
static void *find_fit(size_t asize){
    int class = find_position(asize);
    void *bp = ROOT(class);
    
    while (class < SEGREGATED_SIZE){
        bp = ROOT(class);
        while(bp != NULL){
            if((asize <= GET_SIZE(HDRP(bp)))){
                return bp;
            }
            bp = SUCC(bp);
        }
        class += 1;
    }
    return NULL;
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    // delete_node(bp);
    delete_seglist(bp);

    if ((csize - asize) >= (2*DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        // printf("할당 받은 후, 그 다음 블록의 시작 주소 : %p\n", bp+WSIZE);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        // insert_node(bp);
        insert_seglist(bp);
        // last_fit_pointer = bp; // 검색 시작 위치

    } 
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        // last_fit_pointer = bp;
    }
}

static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    
    if (prev_alloc && !next_alloc){//case 2
       
        delete_seglist(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        
    }

    else if(!prev_alloc && next_alloc) { //case3
        
        delete_seglist(PREV(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        
        
    }

    else if(!prev_alloc && !next_alloc){ //case 4
        
        delete_seglist(PREV_BLKP(bp));
        delete_seglist(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    
    insert_seglist(bp);
    return bp;


}

void mm_free(void *bp){
    
    size_t size = GET_SIZE(HDRP(bp));
    
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    
    coalesce(bp);
}
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
    {
        return NULL;
    }
    
    PUT(HDRP(bp), PACK(size, 0));
   
    PUT(FTRP(bp), PACK(size, 0));
    
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));
    return coalesce(bp);
}
/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    
    if ((heap_listp = mem_sbrk((SEGREGATED_SIZE + 4) * WSIZE)) == (void *)-1)
    {
        return -1;
    }

    
    PUT(heap_listp, 0);
    /*seglist*/
    PUT(heap_listp + (1 * WSIZE), PACK((SEGREGATED_SIZE + 2) * WSIZE,1));//prologue header
    for (int i = 0; i < SEGREGATED_SIZE; i++){
        PUT(heap_listp + (2 + i) * WSIZE, NULL);
    }
    PUT(heap_listp + (SEGREGATED_SIZE + 2) * WSIZE, PACK((SEGREGATED_SIZE + 2) * WSIZE, 1));
    PUT(heap_listp + (SEGREGATED_SIZE + 3) * WSIZE, PACK(0, 1));//epilogue header
    heap_listp += 2 * WSIZE;

    if(extend_heap(CHUNKSIZE/WSIZE) == NULL){
        return -1;
    }
    return 0;
    
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    

    size_t asize;
    size_t extendsize;
    void *bp;

    if(size <= 0)
        return NULL;
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1))/DSIZE);

    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }
    

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */


/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
        copySize = size;
    
    
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}
