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

/* single word (4) or double word (8) alignment */
//메모리의 정렬 값 (ALIGNMENT)을 8 바이트로 설정
#define ALIGNMENT 16

/* rounds up to the nearest multiple of ALIGNMENT */
//이 매크로는 주어진 size를 가장 가까운 ALIGNMENT의 배수 값으로 올림합니다. 
//& ~0x7 연산은 주어진 값을 8의 배수로 만들어줍니다. 
//예를 들어, ALIGN(10)의 경우 결과는 16이 됩니다.
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

//size_t는 C와 C++에서 객체나 배열의 크기를 나타내는 데 사용되는 데이터 유형입니다. 
//SIZE_T_SIZE는 size_t 유형의 크기를 ALIGNMENT의 배수로 올린 값입니다.
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
/*Basic constants and macros*/
#define WSIZE 4
#define DSIZE 8
// 1<<12 연산을 수행하면, 1비트가 12자리 왼쪽으로 이동
// 010000000000  (2의 12승) 즉, 4096
#define CHUNKSIZE (1 << 12)
// x가 y보다 크면 x, x가 y보다 작으면 y
#define MAX(x, y) ((x) > (y) ? (x) : (y))

/*Pack a size and allocated bit into a word*/
// | 연산은 두개의 비트 중 하나라도 1이면 1을 반환한다.
#define PACK(size, alloc) ((size) | (alloc))

/*Read and write a word at address p*/
#define GET(p) (*(unsigned int *)(p))
/*PUT 매크로는 주어진 주소 p에 unsigned int 값 val을 저장하는 역할*/
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/*Read the size and allocated fields from address p*/
// 포인터 p가 가리키는 주소에서 unsigned int 유형의 값을 반환

// GET_SIZE(...): 이 함수는 주어진 주소에서 블록의 크기를 가져옵니다.
// 이 경우, 주어진 주소는 현재 블록의 헤더 주소입니다. 따라서 이 함수는 현재 블록의 크기를 반환합니다.
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/*Given block ptr bp, compute address of its header and footer*/
// 주어진 포인터 bp에서 WSIZE만큼 떨어진 주소를 반환
#define HDRP(bp) ((char *)(bp)-WSIZE)
/*HDRP(bp): 포인터 bp가 가리키는 주소에서 WSIZE만큼 떨어진 주소를 반환합니다.
GET_SIZE(HDRP(bp)): 그 주소에서 unsigned int 유형의 값을 읽습니다. 그 값에서 블록 크기를 나타내는 비트들만 추출합니다 (일반적으로 특정 플래그 비트를 제외한 모든 비트).
따라서, GET_SIZE(HDRP(bp))는 bp가 가리키는 블록의 크기를 반환*/
// FTRP(bp) : bp가 가리키는 블록의 푸터 주소를 반환
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/*Given block ptr bp, compute address of next and previous blocks*/
//((char *)(bp) - WSIZE): 형변환된 bp 포인터에서 WSIZE만큼 떨어진 주소를 반환합니다. 이 주소는 현재 블록의 헤더를 가리킵니다.
//((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE))): 이 부분은 bp 포인터에서 현재 블록의 크기만큼 더한 주소를 반환합니다. 이 주소는 다음 블록의 시작 주소입니다.
// NEXT_BLKP(bp) 매크로는 bp가 가리키는 블록의 다음 블록의 시작 주소를 반환합니다.
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
//((char *)(bp) - DSIZE): 형변환된 bp 포인터에서 DSIZE만큼 떨어진 주소를 반환합니다. 이 주소는 현재 블록의 이전 블록의 푸터를 가리킵니다.
// GET_SIZE(...): 이 함수는 주어진 주소에서 블록의 크기를 가져옵니다. 여기서 주어진 주소는 현재 블록의 이전 블록의 푸터 주소입니다. 따라서 이 함수는 이전 블록의 크기를 반환합니다.
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

/*explicit 매크로*/
#define PREV(bp) (*(void**)(bp))
#define SUCC(bp) (*(void**)(bp + WSIZE))




// static void *last_fit_pointer = NULL; // 마지막으로 검사한 위치를 기억하는 포인터
// static void *last_fit_pointer;
static char *free_listp; // free list head - 가용리스트 시작부분
static void *heap_listp;

/*function*/
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void *coalesce(void *bp);
void delete_node(void *bp);
void insert_node(void *bp);
static void *extend_heap(size_t words);
//explicit
static void *find_fit(size_t asize){
    void *bp;
    for (bp = free_listp; GET_ALLOC(HDRP(bp)) != 1; bp = SUCC(bp)) {
        if ((asize <= GET_SIZE(HDRP(bp)))) {
            // printf("할당 받은 주소 : %p\n", bp);
            return bp;
        }
    }
    return NULL;
}
//implicit
// static void *find_fit(size_t asize){
//     void *bp;
//     for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
//         if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
//             // printf("할당 받은 주소 : %p\n", bp);
//             return bp;
//         }
//     }
//     return NULL;
// }

// void *find_fit(size_t asize) {
//     void *start = last_fit_pointer; // 검색 시작 위치

//     // 초기 시작점이 설정되지 않았다면 heap의 시작으로 설정
//     if (start == NULL) start = heap_listp;

//     // 시작 위치부터 힙의 끝까지 검색
//     for (void *bp = start; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
//         if (!GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp))) {
//             last_fit_pointer = bp; // 위치 정보 업데이트
//             return bp; // 적합한 블록 찾으면 반환
//         }
//         // last_fit_pointer;
//     }

//     // 초기 시작점부터 검색한 위치까지 다시 검색
//     for (void *bp = heap_listp; bp != start; bp = NEXT_BLKP(bp)) {
//         if (!GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp))) {
//             last_fit_pointer = bp; // 위치 정보 업데이트
//             return bp; // 적합한 블록 찾으면 반환
//         }
//     }

//     return NULL; // 적합한 블록을 찾지 못하면 NULL 반환
// }
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    delete_node(bp);

    if ((csize - asize) >= (2*DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        // printf("할당 받은 후, 그 다음 블록의 시작 주소 : %p\n", bp+WSIZE);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        insert_node(bp);
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

    // if(prev_alloc&&next_alloc) {//case 1

    //     last_fit_pointer = bp;
    //     insert_node(bp);
    //     return bp;
    // }
    if (prev_alloc && !next_alloc){//case 2
        /*NEXT_BLKP에 있을 prev와 succ을 del해준다*/
        delete_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        
    }

    else if(!prev_alloc && next_alloc) { //case3
        /*PREV_BLKP에 있을 prev와 succ을 del해준다*/
        delete_node(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        
        
    }

    else if(!prev_alloc && !next_alloc){ //case 4
        delete_node(PREV_BLKP(bp));
        delete_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    // last_fit_pointer = bp;
    /**/
    insert_node(bp);
    return bp;


}
void delete_node(void *bp) {
    //첫 번째 블록을 없앨 때
    if(bp==free_listp){
        PREV(SUCC(bp)) = NULL;
        free_listp = SUCC(bp);
    } else{
        SUCC(PREV(bp)) = SUCC(bp);
        PREV(SUCC(bp)) = PREV(bp);
    }
}

void insert_node(void *bp) {
    SUCC(bp) = free_listp;
    PREV(bp) = NULL;
    PREV(free_listp) = bp;
    free_listp = bp;
}
void mm_free(void *bp){
    //bp의 헤더 크기
    size_t size = GET_SIZE(HDRP(bp));
    /*bp 헤더의 크기 정보와 alloc상태를 0으로 만들어 free로 만들어준다.
    bp 풋터의 크기 정보와 alloc상태를 0으로 만들어 free로 만들어준다*/
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    // printf("free 해준 주소: %p\n", bp);
    coalesce(bp);
}
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /*Allocate an even number of words to maintain alignment*/
    /*words % 2 == 0 이면, False, words * WSIZE 반환
    words % 2 == 1 이면 ,  True, (words+1)*WSIZE 반환
    즉, 짝수면 words에 WSIZE를 곱해준것이 size가 되고,
    홀수면 words+1 에 WSIZE를 곱해주어 size를 짝수로 만들어준다. */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
    {
        return NULL;
    }
    /*Initialize free block header/footer and the epilogue header*/
    /*HDRP(bp):주어진 주소 bp에서 WSIZE만큼 떨어진 값 반환
    PACK(size, 0)은 size 값을 반환 (alloc 비트가 0이기 때문에). 
    즉 주어진 주소에서 WSIZE만큼 떨어진 곳의 값은 - 
    미할당 상태를 나타내며, free block의 header이다.: */
    PUT(HDRP(bp), PACK(size, 0));
    /*FTRP(bp) : bp가 가리키는 블록의 푸터주소 반환, 
    size값을 저장하고, alloc == 0이니 미할당 상태 저장
    */
    PUT(FTRP(bp), PACK(size, 0));
    /*NEXT_BLKP(bp) : bp가 가리키는 블록의 다음 블록 시작주소 반환, 
    PACK(0, 1)블록의 사이즈는 0이며, alloc은 1이다. 즉 할당된 상태를 나타낸다.
    HDRP(): 다음 블록의 시작지점에서 WSIZE만큼 떨어진 값을 반환한다.
    즉 다음블록의 시작지점이며, 이 헤더는 사이즈 정보와 할당상태를 가지고 있다.*/
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1)); //new epilogue header
    return coalesce(bp);
}
/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /*Create the initial empty heap*/
    /*mem_sbrk는 메모리 할당에 실패한 경우 (void*)-1반환한다.
    즉 heap_listp = (void*)-1일 경우, -1을 리턴한다.
    */
    if ((heap_listp = mem_sbrk(6 * WSIZE)) == (void *)-1)
    {
        return -1;
    }

    // heap_listp의 주소에 unsigned int값 0을 저장
    PUT(heap_listp, 0);
    // heap_listp의 주소에서 (n*WSIZE)바이트만큼 증가한 주소 값에 PACK(DSIZE, 1)을 저장한다.
    /*implicit*/
    // PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // plologue header
    // PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // prologue footer
    // PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     // epilogue footer

    /*explicit*/
    PUT(heap_listp + (1*WSIZE), PACK(ALIGNMENT,1)); //프롤로그 헤더 16/1
    PUT(heap_listp + (2*WSIZE), 0); //프롤로그 PREV 포인터 NULL로 초기화
    PUT(heap_listp + (3*WSIZE), 0); //프롤로그 NEXT 포인터 NULL로 초기화
    PUT(heap_listp + (4*WSIZE), PACK(ALIGNMENT, 1)); //프롤로그 풋터 16/1
    PUT(heap_listp + (5*WSIZE), PACK(0, 1)); //에필로그 헤더 0/1
    // heap_listp의 주소값에서 (2*WSIZE) 바이트만큼 증가시킨다
    // heap_listp += (2 * WSIZE);
    free_listp = heap_listp + DSIZE;//free_listp 가 prev 포인터를 가리키게 초기화
    // printf("힙의 시작 주소 : %p\n", heap_listp);
    /*Extend the emplty heap woth a free block of CHUNKSIZE bytes*/
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
    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1)
    //     return NULL;
    // else
    // {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }

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
    // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
        copySize = size;
    // else if (!GET_ALLOC(HDRP(NEXT_BLKP(oldptr))) || !GET_SIZE(HDRP(NEXT_BLKP(oldptr)))) {
    //     extend_heap();
    // }
    
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}
/*
 * mm_realloc - 동적 할당된 메모리 내용 유지하며 할당된 메모리 크기 변경
 */
// void *mm_realloc(void *bp, size_t size)
// {
//     void *new_bp = bp;      /* return할 ptr */
//     size_t new_size = size; /* 요청한 realloc 크기 */
//     int remainder;          /* 적절한 블록 크기 */
//     int extendsize;         /* 힙 확장 크기 */
    
//     /* 거짓 요청시 */
//     if (size == 0)
//         return NULL;
    
//     /* 헤더와 풋터 위한 공간 확보 및 더블 워드 요건 만족시킴 */
//     if (new_size <= DSIZE) {
//         new_size = 2 * DSIZE;
//     } else {
//         new_size = ALIGN(size+DSIZE);
//     }

//     /* 다음 블록이 가용 블록이거나 에필로그 블록인지 확인 */
//     if (!GET_ALLOC(HDRP(NEXT_BLKP(bp))) || !GET_SIZE(HDRP(NEXT_BLKP(bp)))) {
//         remainder = GET_SIZE(HDRP(bp)) + GET_SIZE(HDRP(NEXT_BLKP(bp))) - new_size;
//         if (remainder < 0) {
//             extendsize = MAX(-remainder, CHUNKSIZE);
//             if (extend_heap(extendsize) == NULL)
//                 return NULL;
//             remainder += extendsize;
//         }
        
//         delete_node(NEXT_BLKP(bp));   /* 분할된 채 가용 seglist에 들어있는 다음 블록 삭제 */ 
        
//         PUT(HDRP(bp), PACK(new_size + remainder, 1));
//         PUT(FTRP(bp), PACK(new_size + remainder, 1)); 
//     } else {
//         new_bp = mm_malloc(new_size - DSIZE);  
//         memcpy(new_bp, bp, size); 
//         mm_free(bp);
//     }
//     return new_bp;
// }