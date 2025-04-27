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

#define OVERHEAD DSIZE                         /* header + footer = 8 */
#define MIN_BLOCK_SIZE (OVERHEAD + 2 * sizeof(void *))  /* 8 + 16 = 24 */
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


/* explicit free list payload 필드 위치 */
#define SUCC_PTR(bp)  ((char *)(bp))          /* next 포인터: bp[+0..+7] */
#define PRED_PTR(bp)  ((char *)(bp) + DSIZE)  /* prev 포인터: bp[+8..+15] */
/* 또는 포인터 크기 기반으로:
#define PRED_PTR(bp)  ((char *)(bp) + sizeof(void *))
*/

/* 접근/설정 매크로 (변경 불필요) */
#define SUCC(bp)       (*(char **)(SUCC_PTR(bp)))
#define PRED(bp)       (*(char **)(PRED_PTR(bp)))
#define SET_SUCC(bp,p) (SUCC(bp) = (char *)(p))
#define SET_PRED(bp,p) (PRED(bp) = (char *)(p))





/* 힙 시작 포인터(global) */
static char *heap_listp = NULL;

static char *free_list_head = NULL;  /* explicit free list의 시작점 */
/* 함수 프롤토타입 */
static void *coalesce(void *bp);          /* 인접 가용 블록 병합 */
static void *find_fit(size_t asize);      /* 가용 블록 탐색 */
static void place(void *bp, size_t asize);/* 블록 배치 및 분할 처리 */
static void insert_free_block(void *bp);
static void remove_free_block(void *bp);

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
    
    bp = coalesce(bp);
    insert_free_block(bp);
    return bp;
}

static void insert_free_block(void *bp) {
    SET_SUCC(bp, free_list_head);
    SET_PRED(bp, NULL);
    if (free_list_head)
        SET_PRED(free_list_head, bp);
    free_list_head = bp;
}

static void remove_free_block(void *bp) {
    char *prev = PRED(bp);
    char *next = SUCC(bp);
    if (prev)
        SET_SUCC(prev, next);
    else
        free_list_head = next;
    if (next)
        SET_PRED(next, prev);
}
/* coalesce: 인접 블록이 가용이면 병합 */
static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    /* 인접 블록이 free list에 있을 테니 제거 */
    if (!prev_alloc) remove_free_block(PREV_BLKP(bp));
    if (!next_alloc) remove_free_block(NEXT_BLKP(bp));

    /* 기존 로직으로 size 조정 */
    if (prev_alloc && next_alloc)            { /* nothing */ }
    else if (prev_alloc && !next_alloc)      { size += GET_SIZE(HDRP(NEXT_BLKP(bp))); }
    else if (!prev_alloc && next_alloc)      { size += GET_SIZE(HDRP(PREV_BLKP(bp))); bp = PREV_BLKP(bp); }
    else /* both free */                     { size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); bp = PREV_BLKP(bp); }

    /* header/footer 업데이트 */
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    /* 병합된 블록을 리스트에 재삽입 */
    return bp;
}


/* find_fit: 적당한 크기의 가용 블록 탐색 */
static void *find_fit(size_t asize) {
    void *bp = free_list_head;
    while (bp) {
        size_t bsize = GET_SIZE(HDRP(bp));
        if (bsize >= asize) {
            return bp;
        }
        bp = SUCC(bp);
    }
    return NULL;
}

static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));
    remove_free_block(bp);

    if ((csize - asize) >= MIN_BLOCK_SIZE) {
        /* 분할 후 할당 블록 */
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        /* 남은 부분 free로 만들고 리스트에 삽입 */
        void *next_bp = NEXT_BLKP(bp);
        PUT(HDRP(next_bp), PACK(csize - asize, 0));
        PUT(FTRP(next_bp), PACK(csize - asize, 0));
        insert_free_block(next_bp);
    } else {
        /* 분할 없이 전체 할당 */
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}


/* mm_init: 초기 힙 설정 및 프롤로그/에필로그 블록 생성 */
int mm_init(void)
{
    free_list_head = NULL;   /* explicit free list 초기화 */
    /* 초기 힙 영역 확보(4워드) */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
    return -1;
    
    /* 8바이트 정렬 패딩 */
    PUT(heap_listp, 0);
    /* 프롤로그 헤더(크기=8, 할당됨) */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    /* 프롤로그 푸터(크기=8, 할당됨) */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    /* 에필로그 헤더(크기=0, 할당됨) */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));
    /* heap_listp를 프롤로그 블록의 페이로드 시작으로 이동 */
    heap_listp += (2 * WSIZE);
    
    /* 힙을 CHUNKSIZE 바이트 만큼 확장하여 첫 가용 블록 생성 */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    if (extend_heap(4) == NULL)   // 자주 사용되는 작은 블럭이 잘 처리되어 점수가 오름
        return -1;
    return 0;
}


/*
 * mm_malloc - brk 포인터를 증가시켜 블록을 할당합니다.
 *     항상 정렬 단위(8바이트)의 배수 크기로 블록을 할당합니다.
 */
void *mm_malloc(size_t size)
{
    /* 요청 크기가 0이면 NULL 반환 */
    if (size == 0)
        return NULL;

    /* 1) asize 계산: payload+헤더/푸터 올림 정렬 */
    size_t asize = ALIGN(size + OVERHEAD);
    /* 2) explicit 리스트를 위한 최소 크기 보장 */
    if (asize < MIN_BLOCK_SIZE)
        asize = MIN_BLOCK_SIZE;

    /* 3) free list에서 맞는 블록 찾기 */
    void *bp = find_fit(asize);
    if (bp != NULL) {
        place(bp, asize);
        return bp;
    }

    /* 4) 없으면 힙 확장 */
    size_t extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}


/*
 * mm_free - 블록을 해제하고 인접한 가용 블록과 병합(coalesce)합니다.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp)); // 블록의 전체 크기 획득

    PUT(HDRP(bp), PACK(size, 0));     // 헤더를 가용 상태로 설정
    PUT(FTRP(bp), PACK(size, 0));     // 푸터를 가용 상태로 설정
    bp = coalesce(bp);
    insert_free_block(bp);
}

/*
 * mm_realloc - realloc을 malloc과 free 기반으로 구현
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
        remove_free_block(next);
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