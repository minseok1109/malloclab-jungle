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

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "team 6",
    /* First member's full name */
    "Bang min seok",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
#define WSIZE 4             // word와 헤더, footer 사이즈 (바이트)
#define DSIZE 8             // 더블 워드 사이즈 (바이트)
#define CHUNKSIZE (1 << 12) // 이 만큼 힙사이즈를 증가시킴 크기: 4096

#define MAX(x, y) ((x) > (y) ? (x) : (y))

// word에 크기와 할당된 비트를 패킹함
#define PACK(size, alloc) ((size) | (alloc))

// 주소 p에 word를 읽고 씀
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

// 주소 p에서 크기와 할당된 필드를 읽습니다.
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1) // 할당된 블록인지 아닌지 체크

// 주어진 블록 포인터 ptr로 이 블록의 헤더와 푸터의 주소를 계산합니다.
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// 주어진 블록 포인터 ptr로 다음과 이전 블록의 주소를 계산합니다.
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

static char *heap_listp = 0;
static char *start_nextfit = 0;

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 그전 블록으로 가서 그 블록의 가용여부를 확인
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 그 뒷 블록의 가용 여부 확인.
    size_t size = GET_SIZE(HDRP(bp));                   // 지금 블록의 사이즈 확인

    if (prev_alloc && next_alloc)
    { // case 1 - 이전과 다음 블록이 모두 할당 되어있는 경우, 현재 블록의 상태는 할당에서 가용으로 변경
        start_nextfit = bp;
        return bp; // 이미 free에서 가용이 되어있으니 여기선 따로 free 할 필요 없음.
    }
    else if (prev_alloc && !next_alloc)
    {                                          // case2 - 이전 블록은 할당 상태, 다음 블록은 가용상태. 현재 블록은 다음 블록과 통합 됨.
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 다음 블록의 헤더를 보고 그 블록의 크기만큼 지금 블록의 사이즈에 추가한다.
        PUT(HDRP(bp), PACK(size, 0));          // 헤더 갱신(더 큰 크기로 PUT)
        PUT(FTRP(bp), PACK(size, 0));          // 푸터 갱신
    }
    else if (!prev_alloc && next_alloc)
    { // case 3 - 이전 블록은 가용상태, 다음 블록은 할당 상태. 이전 블록은 현재 블록과 통합.
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));            // 푸터에 먼저 조정하려는 크기로 상태 변경한다.
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 현재 헤더에서 그 앞블록의 헤더 위치로 이동한 다음에, 조정한 size를 넣는다.
        bp = PREV_BLKP(bp);                      // bp를 그 앞블록의 헤더로 이동(늘린 블록의 헤더이니까.)
    }
    else
    {                                                                          // case 4- 이전 블록과 다음 블록 모두 가용상태. 이전,현재,다음 3개의 블록 모두 하나의 가용 블록으로 통합.
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 이전 블록 헤더, 다음 블록 푸터 까지로 사이즈 늘리기
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));                               // 헤더부터 앞으로 가서 사이즈 넣고
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));                               // 푸터를 뒤로 가서 사이즈 넣는다.
        bp = PREV_BLKP(bp);                                                    // 헤더는 그 전 블록으로 이동.
    }
    start_nextfit = bp;
    return bp; // 4개 케이스중에 적용된거로 bp 리턴
}

static void *extend_heap(size_t words)
{ // 새 가용 블록으로 힙 확장, 예시로는 2의 10승만큼 워드블록을 만들어라.
    char *bp;
    size_t size; // size_t = unsigned int, 이 함수에서 넣을 size를 하나 만들어줌.
    /* alignment 유지를 위해 짝수 개수의 words를 Allocate */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    // 홀수가 나오면 사이즈를 한번 더 재정의. 힙에서 늘릴 사이즈를 재정의.
    if ((long)(bp = mem_sbrk(size)) == -1)
    { // sbrk로 size로 늘려서 long 형으로 반환한다.(한번 쫙 미리 늘려놓는 것) mem_sbrk가 반환되면 bp는 현재 만들어진 블록의 끝에 가있음.
        return NULL;
    } // 사이즈를 늘릴 때마다 old brk는 과거의 mem_brk위치로 감.

    // bp는 늘어만 메모리의 시작 주소를 나타냄

    /* free block 헤더와 푸터를 init하고 epilogue 헤더를 init*/
    PUT(HDRP(bp), PACK(size, 0));         // free block header 생성. /(prologue block이랑 헷갈리면 안됨.) regular block의 총합의 첫번째 부분. 현재 bp 위치의 한 칸 앞에 헤더를 생성.
    PUT(FTRP(bp), PACK(size, 0));         // free block footer / regular block 총합의 마지막 부분.
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 블록을 추가했으니 epilogue header를 새롭게 위치 조정해줌. (HDRP: 1워드 뒤에 있는 것을 지칭.
    // 처음 세팅의 의미 = bp를 헤더에서 읽은 사이즈만큼 이동하고, 앞으로 한칸 간다. 그위치가 결국 늘린 블록 끝에서 한칸 간거라 거기가 epilogue header 위치.

    /* 만약 prev block이 free였다면, coalesce해라.*/
    return coalesce(bp); // 처음에는 coalesc를 할게 없지만 함수 재사용을 위해 리턴값으로 선언
}

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{ // 처음에 heap을 시작할 때 0부터 시작. 완전 처음.(start of heap)
    /* create 초기 빈 heap*/
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
    { // old brk에서 4만큼 늘려서 mem brk로 늘림.
        return -1;
    }
    PUT(heap_listp, 0);                            // 블록생성시 넣는 padding을 한 워드 크기만큼 생성. heap_listp 위치는 맨 처음.
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // prologue header 생성. pack을 해석하면, 할당을(1) 할건데 8만큼 줄거다(DSIZE). -> 1 WSIZE 늘어난 시점부터 PACK에서 나온 사이즈를 줄거다.)
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // prologue footer생성.
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     // epilogue block header를 처음에 만든다. 그리고 뒤로 밀리는 형태.
    heap_listp += (2 * WSIZE);                     // prologue header와 footer 사이로 포인터로 옮긴다. header 뒤 위치. 다른 블록 가거나 그러려고.
    start_nextfit = heap_listp;

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) // extend heap을 통해 시작할 때 한번 heap을 늘려줌. 늘리는 양은 상관없음.
        return -1;
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 * brk 포인터를 증가시켜 블록을 할당합니다.
 * 항상 크기가 정렬의 배수인 블록을 할당합니다.
 */

static void *find_fit(size_t asize)
{ // next fit 검색을 수행
    void *bp;

    for (bp = start_nextfit; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
            return bp;
    }
    for (bp = heap_listp; bp != start_nextfit; bp = NEXT_BLKP(bp)) // 위에서 못찾은 걸 처음으로 돌아가서 다시 탐색 -> next_fit방식
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
            return bp;
    }
    return NULL;
}

static void place(void *bp, size_t asize)
{                                      /*들어갈 위치를 포인터로 받는다.(find fit에서 찾는 bp) 크기는 asize로 받음.
                                         요청한 블록을 가용 블록의 시작 부분에 배치, 나머지 부분의 크기가 최소 블록크기와 같거나 큰 경우에만 분할하는 함수.*/
    size_t csize = GET_SIZE(HDRP(bp)); // 현재 있는 블록의 사이즈.
    if ((csize - asize) >= (2 * DSIZE))
    {                                          // 현재 블록 사이즈안에서 asize를 넣어도 2*DSIZE(헤더와 푸터를 감안한 최소 사이즈)만큼 남냐? 남으면 다른 data를 넣을 수 있으니까.
        PUT(HDRP(bp), PACK(asize, 1));         // 헤더위치에 asize만큼 넣고 1(alloc)로 상태변환. 원래 헤더 사이즈에서 지금 넣으려고 하는 사이즈(asize)로 갱신.(자르는 효과)
        PUT(FTRP(bp), PACK(asize, 1));         // 푸터 위치도 변경.
        bp = NEXT_BLKP(bp);                    // regular block만큼 하나 이동해서 bp 위치 갱신.
        PUT(HDRP(bp), PACK(csize - asize, 0)); // 나머지 블록은(csize-asize) 다 가용하다(0)하다라는걸 다음 헤더에 표시.
        PUT(FTRP(bp), PACK(csize - asize, 0)); // 푸터에도 표시.
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1)); // 위의 조건이 아니면 asize만 csize에 들어갈 수 있으니까 내가 다 먹는다.
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

void *mm_malloc(size_t size)
{
    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1)
    //     return NULL;
    // else
    // {
    // *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }

    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0) // 이상한 요청  무시
        return NULL;

    if (size <= DSIZE)
    {
        asize = 2 * DSIZE; // 최소 16바이트의 크기로 만들어주기
    }
    else
    {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE); // 16바이트가 넘어가면 인접한 8의 배수로 반올림
    }
    bp = find_fit(asize); // 할당할 공간 찾기
    if (bp != NULL)       // bp가 널이 아니면
    {
        place(bp, asize); // 할당하기
        return bp;
    }

    /*공간이 부족해서 할당하지 못한 경우 확장시킨 다음에 할당을 다시 시도*/
    extendsize = MAX(asize, CHUNKSIZE);
    bp = extend_heap(extendsize / WSIZE);
    if (bp == NULL)
    {
        return NULL;
    }
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *
mm_realloc(void *ptr, size_t size)
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
    /*memcpy(new, old, size)
    new -> 복사받을 메모리를 가리키는 포인터
    old -> 복사할 메모리를 가지고 있는 포인터
    size -> 복사할 데이터의 길이*/
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}
