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
    "jungle6_week06_6",
    /* First member's full name */
    "KimHyeonji",
    /* First member's email address */
    "hyeonji0718 @gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

#define WSIZE sizeof(void *) // pointer의 크기 (32bit -> WSIZE = 4 / 64bit -> WSIZE = 8)
#define DSIZE (2 * WSIZE)    // double word size
#define MINIMUM 8
#define CHUNKSIZE (1 << 12)
#define LISTLIMIT 20

#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(ptr) ((char *)(ptr)-WSIZE)
#define FTRP(ptr) ((char *)(ptr) + GET_SIZE(HDRP(ptr)) - DSIZE)

#define NEXT_BLKP(ptr) ((char *)(ptr) + GET_SIZE(((char *)(ptr)-WSIZE)))
#define PREV_BLKP(ptr) ((char *)(ptr)-GET_SIZE(((char *)(ptr)-DSIZE)))

#define PREC_FREEP(ptr) (*(void **)(ptr))
#define SUCC_FREEP(ptr) (*(void **)(ptr + WSIZE))

static char *heap_listp;
static void *seg_list[LISTLIMIT];

static void *extend_heap(size_t words);
static void *coalesce(void *ptr);
static void *find_fit(size_t asize);
static void place(void *ptr, size_t newsize);

int mm_init(void);
void *mm_malloc(size_t size);
void mm_free(void *ptr);
void *mm_realloc(void *ptr, size_t size);

int mm_init(void)
{
    // 전역 변수로  선언한  seglist를 NULL로 초기화
    for (int i = 0; i < LISTLIMIT; i++)
    {
        seg_list[i] = NULL;
    }
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(MINIMUM, 1));
    PUT(heap_listp + (2 * WSIZE), PACK(MINIMUM, 1));
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));
    heap_listp = heap_listp + 2 * WSIZE;

    if (extend_heap(4) == NULL)
    {
        return -1;
    }

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
    {
        return -1;
    }
    return 0;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : (words)*WSIZE;
    if (((bp = mem_sbrk(size)) == (void *)-1))
    {
        return NULL;
    }

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *ptr;

    /* 의미 없는 요청 처리 안함 */
    if (size == 0)
    {
        return NULL;
    }
    if (size <= DSIZE)
    {
        asize = 2 * DSIZE;
    }
    else
    {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }

    if ((ptr = find_fit(asize)) != NULL)
    {
        place(ptr, asize);
        return ptr;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((ptr = extend_heap(extendsize / WSIZE)) == NULL)
    {
        return NULL;
    }
    place(ptr, asize);
    return ptr;
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc)
    {
        put_free_block(bp, size);
        return bp;
    }
    else if (prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        remove_block(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        remove_block(PREV_BLKP(bp));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        remove_block(PREV_BLKP(bp));
        remove_block(NEXT_BLKP(bp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    put_free_block(bp, size);
    return bp;
}

static void *find_fit(size_t asize)
{
    void *bp;
    int list = 0;
    size_t searchsize = asize;

    while (list < LISTLIMIT)
    {
        /* list(0~19) 가용블록을 못찾고 19번째 리스트에 도달하거나, 나보다 큰 사이즈의
        seg_list가 NULL이 아니면 */
        if ((list == LISTLIMIT - 1) || (searchsize <= 1) && (seg_list[list] != NULL))
        {
            bp = seg_list[list];
            while ((bp != NULL) && (asize > GET_SIZE(HDRP(bp))))
            {
                bp = SUCC_FREEP(bp);
            }
            if (bp != NULL)
            {
                return bp;
            }
        }
        searchsize >>= 1;
        list++;
    }
    return NULL;
}

// place(ptr, size): 요구 메모리를 할당할 수 있는 가용 블록을 할당한다. 이 때 분할이 가능하면 분할한다.
static void place(void *ptr, size_t asize)
{
    // 현재 할당할 수 있는 후보 가용 블록의 주소
    size_t csize = GET_SIZE(HDRP(ptr));

    // 할당될 블록이므로 free list에서 없애준다.
    remove_block(ptr);
    // 필요한 블록 빼고 남는게 16바이트 이상이면
    if ((csize - asize) >= (2 * DSIZE))
    {
        // 할당처리
        PUT(HDRP(ptr), PACK(asize, 1));
        PUT(FTRP(ptr), PACK(asize, 1));
        ptr = NEXT_BLKP(ptr); // ptr를 다음블록으로
        // 나머지 사이즈 free처리
        PUT(HDRP(ptr), PACK(csize - asize, 0));
        PUT(FTRP(ptr), PACK(csize - asize, 0));
        coalesce(ptr);
        // 이때 연결돼있는게 있을 수 있으므로 coalesce
    }
    else
    {
        PUT(HDRP(ptr), PACK(csize, 1));
        PUT(FTRP(ptr), PACK(csize, 1));
    }
}

// 오름차순으로 정렬된 seq list에서 크기에 맞게 탐색하여 삽입
void put_free_block(void *ptr, size_t size)
{
    int idx = 0;
    void *search_ptr;
    void *insert_ptr = NULL; // searchptr의 값을 저장해놓는 용도

    // size의 비트를 1씩 오른쪽으로 shift 시키며(2씩 나누면서), size class 리스트에 할당될 인덱스 설정
    while ((idx < LISTLIMIT - 1) && (size > 1))
    {
        size >>= 1;
        idx++;
    }

    search_ptr = seg_list[idx];
    // 넘겨받은 사이즈 보다 큰 사이즈 나올때까지 탐색
    while ((search_ptr != NULL) && (size > GET_SIZE(HDRP(search_ptr))))
    {
        insert_ptr = search_ptr;             // 가용블록을 추가할 size class 리스트의 위치 저장
        search_ptr = SUCC_FREEP(search_ptr); //
    }

    if (search_ptr != NULL)
    {
        if (insert_ptr != NULL) // 리스트 중간에 삽입할 때
        {
            SUCC_FREEP(ptr) = search_ptr;
            PREC_FREEP(ptr) = insert_ptr;
            PREC_FREEP(search_ptr) = ptr;
            SUCC_FREEP(insert_ptr) = ptr;
        }
        else // 리스트에 노드가 있으면서 맨 앞에 삽입할 때
        {
            SUCC_FREEP(ptr) = search_ptr;
            PREC_FREEP(ptr) = NULL;
            PREC_FREEP(search_ptr) = ptr;
            seg_list[idx] = ptr;
        }
    }
    else
    {
        if (insert_ptr != NULL) // 리스트에 노드가 있으면서 제일 마지막에 삽입할 때 -> 가장 큰 블록을 삽입할 때
        {
            SUCC_FREEP(ptr) = NULL;
            PREC_FREEP(ptr) = insert_ptr;
            SUCC_FREEP(insert_ptr) = ptr;
        }
        else // 처음 삽입할 때
        {
            SUCC_FREEP(ptr) = NULL;
            PREC_FREEP(ptr) = NULL;
            seg_list[idx] = ptr;
        }
    }
    return;
}

// remove_block(ptr) : 할당되거나 연결되는 가용 블록을 free list에서 없앤다.
void remove_block(void *ptr)
{
    int idx = 0;
    size_t size = GET_SIZE(HDRP(ptr));

    while ((idx < LISTLIMIT - 1) && (size > 1))
    { // 지우려는 list idx 탐색
        size >>= 1;
        idx++;
    }

    if (SUCC_FREEP(ptr) != NULL)
    { // successor != NULL이면
        if (PREC_FREEP(ptr) != NULL)
        { // predecessor != NULL 중간에있는걸 지우는경우
            PREC_FREEP(SUCC_FREEP(ptr)) = PREC_FREEP(ptr);
            SUCC_FREEP(PREC_FREEP(ptr)) = SUCC_FREEP(ptr);
        }
        else
        { // pred 블록이 NULL일 경우
            // 리스트 맨 앞의 블록을 지울 경우
            PREC_FREEP(SUCC_FREEP(ptr)) = NULL;
            seg_list[idx] = SUCC_FREEP(ptr);
        }
    }
    else
    { // successor == NULL
        if (PREC_FREEP(ptr) != NULL)
        { // 리스트 맨 끝 블록인 경우
            SUCC_FREEP(PREC_FREEP(ptr)) = NULL;
        }
        else
        { // 하나만 있었을 경우
            seg_list[idx] = NULL;
        }
    }
    return;
}

// free되면 가용블록끼리 합쳐주고 header, footer 갱신
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0)); // 헤더 갱신
    PUT(FTRP(ptr), PACK(size, 0)); // 푸터 갱신
    coalesce(ptr);                 // 합치기
}
// realloc은 malloc으로 새로 할당하고 그 전에 있는 것은 free해줌

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
    memcpy(newptr, oldptr, copySize); // oldptr로부터 copySize만큼 깊은복사
    mm_free(oldptr);
    return newptr;
}