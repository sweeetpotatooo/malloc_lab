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
    "puddingjelly",
    /* First member's full name */
    "sweeetpotatooo",
    /* First member's email address */
    "sehyun5004@naver.com",
    /* Second member's full name (leave blank if none) */
    "minmooo-ya",
    /* Second member's email address (leave blank if none) */
    "minhyay01@gmail.com"};

/* 단일 워드(4바이트) 또는 더블 워드(8바이트) 정렬 기준 */
#define ALIGNMENT 8

/* ALIGNMENT 배수로 올림 */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

/* size_t 타입 크기를 ALIGNMENT 배수로 정렬한 크기 */
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* 워드 및 더블 워드 크기 */
#define WSIZE 4 /* 워드 크기(헤더/푸터) */
#define DSIZE 8 /* 더블 워드 크기(정렬 단위) */

/* 힙 확장 시 요청할 최소 크기(4096바이트) */
#define CHUNKSIZE (1<<12)

/* 최대/최소 계산 매크로 */
#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* 블록 크기와 할당 비트 결합 */
#define PACK(size, alloc) ((size) | (alloc))

/* 메모리 읽기/쓰기 매크로 */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* 헤더에서 블록 크기 및 할당 여부 추출 */
#define GET_SIZE(p) (GET(p) & ~0x7)   /* 하위 3비트를 제외한 크기 */
#define GET_ALLOC(p) (GET(p) & 0x1)   /* 하위 1비트가 할당 상태 */

/* 블록 포인터 bp로부터 헤더/푸터 주소 계산 */
#define HDRP(bp) ((char *)(bp) - WSIZE)                                      /* 헤더 위치 */
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)                 /* 푸터 위치 */

/* 다음/이전 블록으로 이동 */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))      /* 다음 블록 포인터 */
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))      /* 이전 블록 포인터 */

/* 힙 시작 포인터(global) */
static char *heap_listp = NULL;

/* 함수 프로토타입 */
static void *coalesce(void *bp);          /* 인접 가용 블록 병합 */
static void *find_fit(size_t asize);      /* 가용 블록 탐색 */
static void place(void *bp, size_t asize);/* 블록 배치 및 분할 처리 */

/* 힙을 words * WSIZE 바이트 만큼 확장하고 새로운 가용 블록 생성 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* 짝수 워드로 맞추어 8바이트 정렬 유지 */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* 새로 생성된 블록의 헤더와 푸터 설정 (가용 상태) */
    PUT(HDRP(bp), PACK(size, 0));              /* 가용 블록 헤더 */
    PUT(FTRP(bp), PACK(size, 0));              /* 가용 블록 푸터 */
    /* 새로운 에필로그 블록 헤더 설정 (크기=0, 할당됨) */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp); /* 인접 블록과 병합하여 커다란 블록 반환 */
}

/* coalesce: 인접 블록이 가용이면 병합 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); /* 이전 블록 할당 여부 */
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); /* 다음 블록 할당 여부 */
    size_t size = GET_SIZE(HDRP(bp));                   /* 현재 블록 크기 */

    /* Case1: 이전과 다음 모두 할당됨 */
    if (prev_alloc && next_alloc) {
        return bp;
    }
    /* Case2: 이전 할당, 다음 가용 */
    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));         /* 다음 블록 크기 추가 */
        PUT(HDRP(bp), PACK(size, 0));                  /* 병합된 헤더 */
        PUT(FTRP(bp), PACK(size, 0));                  /* 병합된 푸터 */
    }
    /* Case3: 이전 가용, 다음 할당 */
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));         /* 이전 블록 크기 추가 */
        PUT(FTRP(bp), PACK(size, 0));                  /* 병합된 푸터 */
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));       /* 병합된 헤더 */
        bp = PREV_BLKP(bp);                            /* 병합 후 새 블록 포인터 */
    }
    /* Case4: 이전과 다음 모두 가용 */
    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        /* 이전 헤더와 다음 푸터를 병합된 크기로 설정 */
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

/* find_fit: first-fit 전략으로 적당한 크기의 가용 블록 탐색 */
static void *find_fit(size_t asize)
{
    /* 힙의 프로로그 블록 다음부터 에필로그 전까지 순회 */
    for (void *bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp))) {
            return bp; /* 크기가 충분한 가용 블록 발견 */
        }
    }
    return NULL; /* 적합한 블록 없으면 NULL 반환 */
}

/* place: 가용 블록 bp에 asize 크기로 할당, 남으면 분할 처리 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); /* 현재 블록 크기 */

    /* 남은 공간이 최소 블록 크기(16바이트) 이상이면 분할 */
    if ((csize - asize) >= (2 * DSIZE)) {
        /* 할당 블록 헤더/푸터 설정 */
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        /* 남는 공간 가용 블록으로 헤더/푸터 설정 */
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    } else {
        /* 분할 없이 전체 블록 할당 */
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/* mm_init: 초기 힙 설정 및 프로로그/에필로그 블록 생성 */
int mm_init(void)
{
    /* 초기 힙 영역 확보(4워드) */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    /* 8바이트 정렬 패딩 */
    PUT(heap_listp, 0);
    /* 프로로그 헤더(크기=8, 할당됨) */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    /* 프로로그 푸터(크기=8, 할당됨) */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    /* 에필로그 헤더(크기=0, 할당됨) */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));
    /* heap_listp를 프로로그 블록의 페이로드 시작으로 이동 */
    heap_listp += (2 * WSIZE);

    /* 힙을 CHUNKSIZE 바이트 만큼 확장하여 첫 가용 블록 생성 */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    if (extend_heap(4) == NULL)   // 자주 사용되는 작은 블럭이 잘 처리되어 점수가 오름
        return -1;
    return 0;
}

   
/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
/* Return a pointer to a block of at least <size> bytes. */
void *mm_malloc(size_t size)
{
    size_t asize;        /* Adjusted block size                */
    size_t extendsize;   /* Amount to extend heap if no fit    */
    char  *bp;

    /* 1. Ignore zero-byte requests */
    if (size == 0)
        return NULL;

    /* 2. Adjust block size to include overhead & alignment reqs */
    if (size <= DSIZE)               /* 최소 블록 = header+footer+8B payload */
        asize = 2 * DSIZE;           /* 16B */
    else
        asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);

    /* 3. Search the free list for a fit (first-fit) */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);            /* 필요하면 분할 후 배치 */
        return bp;
    }

    /* 4. No fit found – extend the heap and place the block */
    extendsize = MAX(asize, CHUNKSIZE);          /* 최소 CHUNKSIZE 만큼 확장 */
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;

    place(bp, asize);
    return bp;
}


/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
 
void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL)
        return mm_malloc(size);
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    size_t oldsize = GET_SIZE(HDRP(ptr));
    size_t asize = (size <= DSIZE) ? (2 * DSIZE) : DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    if (asize <= oldsize)
        return ptr;

    void *next = NEXT_BLKP(ptr);
    if (!GET_ALLOC(HDRP(next)) && (oldsize + GET_SIZE(HDRP(next))) >= asize) {
        size_t newsize = oldsize + GET_SIZE(HDRP(next));
        PUT(HDRP(ptr), PACK(newsize, 1));
        PUT(FTRP(ptr), PACK(newsize, 1));
        return ptr;
    }

    void *newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;

    size_t copySize = oldsize - DSIZE;
    if (size < copySize)
        copySize = size;
    memcpy(newptr, ptr, copySize);
    mm_free(ptr);
    return newptr;
}