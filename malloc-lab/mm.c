#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

#define WSIZE 8             // Word size (8 bytes)
#define DSIZE 16            // Double word size (16 bytes)
#define CHUNKSIZE (1<<12)   // Heap 확장 단위 (그대로 두어도 OK)

#define MAX(x, y) ((x) > (y) ? (x) : (y))

// Pack a size and allocated bit into a word
#define PACK(size, alloc) ((size) | (alloc))

// Read and write a word at address p
#define GET(p) (*(unsigned long *)(p))  
#define PUT(p, val) (*(unsigned long *)(p) = (val))

// Read the size and allocated fields from address p
#define GET_SIZE(p) (GET(p) & ~(size_t)0xF) // 0xF로 하자 (하위 4비트 사용)
#define GET_ALLOC(p) (GET(p) & 0x1)

// Given block ptr bp, compute address of its header and footer
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// Given block ptr bp, compute address of next and previous blocks
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define PRED(bp) (*(void **)(bp))                        // 이전 free block 포인터
#define SUCC(bp) (*(void **)((char *)(bp) + WSIZE))       // 다음 free block 포인터
/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "puddingjelly",
    /* First member's full name */
    "sweetpotatooo",
    /* First member's email address */
    "sehyun5004@naver.com",
    /* Second member's full name (leave blank if none) */
    "minmoooya",
    /* Second member's email address (leave blank if none) */
    "minhyay01@gmail.com"};

#define ALIGNMENT 16
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0xF)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void *coalesce(void *bp);
static void insert_node(void *bp);
static void remove_node(void *bp);

void *heap_listp;   // 항상 heap의 첫 payload를 가리키는 포인터 (heap base)
static char *free_listp = NULL;  // 명시적 가용 리스트의 헤드 포인터
static void *last_bp = NULL;

static void insert_node(void *bp) {
    if (bp == NULL) return;
    
    // 방어: free_listp가 NULL이 아니고, bp랑 같은 경우는 막아야 함
    if (bp == free_listp) return;

    SUCC(bp) = free_listp;  // bp의 후임자 = 현재 free_listp
    PRED(bp) = NULL;        // bp는 리스트의 제일 앞에 들어가니까 predecessor 없음

    if (free_listp != NULL)
        PRED(free_listp) = bp;  // 기존 free_listp의 predecessor를 bp로 연결

    free_listp = bp;  // free_listp 갱신: 새로 추가한 bp가 리스트 맨 앞
}

static void remove_node(void *bp) {
    if (bp == last_bp) {
        last_bp = SUCC(bp); // 다음 free block으로 옮기기
    }
    if (PRED(bp)) {
        SUCC(PRED(bp)) = SUCC(bp);
    }
    else {
        free_listp = SUCC(bp);
    }
    if (SUCC(bp)) {
        PRED(SUCC(bp)) = PRED(bp);
    }
}


static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));  //  이전 블록 할당 여부
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));  //  다음 블록 할당 여부
    size_t size = GET_SIZE(HDRP(bp));  //  전체 블록 크기

    void *next = NEXT_BLKP(bp);
    void *prev = PREV_BLKP(bp);

    //  case 1 : 이전/다음 모두 할당 된 경우 => 병합 불가
    if (prev_alloc && next_alloc)
    {
        insert_node(bp);
        return bp;
    }

    // case 2 : 다음 블록만 free => 다음 블록과 병합
    else if (prev_alloc && !next_alloc)
    {
        remove_node(next);
        size += GET_SIZE(HDRP(next));  //  크기 확장
        PUT(HDRP(bp), PACK(size, 0));           //  header 갱신
        PUT(FTRP(bp), PACK(size, 0));           //  footer 갱신
    }

    // case 3 : 이전 블록만 free => 이전 블록과 병합
    else if (!prev_alloc && next_alloc)
    {
        remove_node(prev);
        size += GET_SIZE(HDRP(prev));      //  크기 확장
        PUT(FTRP(bp), PACK(size, 0));               //  footer 갱신 (현재 블록 기준)
        PUT(HDRP(prev), PACK(size, 0));    //  이전 블록의 header 갱신
        bp = PREV_BLKP(bp);         //  병합 후 위치 이동

    }

    // case 4 : 이전/다음 모두 free => 세 개 병합
    else
    {
        remove_node(prev);
        remove_node(next);
        size += GET_SIZE(HDRP(prev)) + GET_SIZE(HDRP(next));
        PUT(HDRP(prev), PACK(size, 0));
        PUT(FTRP(next), PACK(size, 0));
        bp = prev;
    }
    insert_node(bp);
    return bp;
}


static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
    return coalesce(bp);
}
int mm_init(void)
{
    //  1. 힙을 위한 최소 공간 16바이트 확보 (padding + prologue header/footer + epilogue header)
    free_listp = NULL;
    heap_listp = mem_sbrk(4 * WSIZE);
    if (heap_listp == (void *)-1) {
        return -1;  //  sbrk 실패 시 에러 리턴
    }
    //  2. 초기 블록들 구성하는 단계
    PUT(heap_listp, 0);                                 //  Alignment padding
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));      //  Prologue header (8바이트, 할당됨)
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));      //  Prologue footer
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));          //  Epilogue header (0바이트, 할당됨)

    //  3. payload 기준 위치로 이동 (Prologue 블록의 payload 포인터)
    heap_listp += (2 * WSIZE);

    void *bp = extend_heap(CHUNKSIZE/WSIZE);
    //  4. 살제 usable한 free block 확보
    if (bp == NULL)
        return -1;
    if (extend_heap(4) == NULL)   // 자주 사용되는 작은 블럭이 잘 처리되어 점수가 오름
        return -1;

    bp = coalesce(bp);
    free_listp = bp;
    last_bp = free_listp;
    return 0;
}
static void *find_fit(size_t asize) {
    void *bp = last_bp ? SUCC(last_bp) : free_listp; // last_bp 다음부터 시작
    void *start = bp; // 처음 시작점 기억

    // 첫 번째 탐색: last_bp 이후부터 끝까지
    for (; bp != NULL; bp = SUCC(bp)) {
        if (GET_SIZE(HDRP(bp)) >= asize) {
            last_bp = bp; // last_bp 갱신
            return bp;
        }
    }

    // 두 번째 탐색: 리스트의 처음부터 last_bp까지
    for (bp = free_listp; bp != start; bp = SUCC(bp)) {
        if (GET_SIZE(HDRP(bp)) >= asize) {
            last_bp = bp; // last_bp 갱신
            return bp;
        }
    }

    // 못 찾으면 NULL
    return NULL;
}
// 주어진 위치에 메모리를 배치 (필요 시 분할)
void place(void *bp, size_t asize)
{
    size_t block_size = GET_SIZE(HDRP(bp));
    size_t remain_size = block_size - asize;

    remove_node(bp);  // 어차피 할당할 거니까 먼저 제거

    // 충분히 분할 가능한 경우
    if (remain_size >= (2 * DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        void *next_bp = NEXT_BLKP(bp);
        PUT(HDRP(next_bp), PACK(remain_size, 0));
        PUT(FTRP(next_bp), PACK(remain_size, 0));
        insert_node(next_bp);  // 새로 생긴 free 블록 등록
    }
    else {
        // 그냥 전체 블록을 할당
        PUT(HDRP(bp), PACK(block_size, 1));
        PUT(FTRP(bp), PACK(block_size, 1));
    }
}
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0) {
        return NULL;
    }

    if (size <= DSIZE) {
        asize = 2*DSIZE;
    }
    else {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE -1)) / DSIZE);
    }

    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) {
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

void *mm_realloc(void *ptr, size_t size)
{
    // NULL ptr은 malloc
    if (ptr == NULL)
        return mm_malloc(size);

    // size == 0 이면 free 후 NULL 반환
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    // 현재 payload 크기 계산 (블록 전체 크기 - header/​footer 오버헤드)
    size_t old_payload = GET_SIZE(HDRP(ptr)) - DSIZE;

    // 줄어드는 요청인 경우, 기존 블록 그대로 반환 (데이터 보존)
    if (size <= old_payload) {
        return ptr;
    }

    // 늘어나는 경우: 새 블록 할당
    void *newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;

    // 옛 블록의 payload 만큼만 복사
    memcpy(newptr, ptr, old_payload);

    // 옛 블록 해제
    mm_free(ptr);
    return newptr;
}
