/* malloc: single free list + first fit */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif

/* single word (4) or double word (8) alignment */
#define WSIZE 4
#define DSIZE 8

/* size of a block with header, list pointers and footer */
#define ESIZE 2 * DSIZE
#define CHUNKSIZE (1 << 12)

#define ALIGNMENT 8
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* store the size and the allocated bit in one word  */
#define PACK(size, alloc) ((size) | (alloc))

/* read and write a word at address p */
#define READ(p)       (*(unsigned int *)(p))
#define WRITE(p, val) (*(unsigned int *)(p) = (val))

/* read the header info from address p */
#define GET_SIZE(p)  (READ(p) & ~0x7)
#define GET_ALLOC(p) (READ(p) & 0x1)

/* given block ptr bp, compute address of header and footer */
#define GET_HEADER(bp) ((char *)(bp) - WSIZE)
#define GET_FOOTER(bp) ((char *)(bp) + GET_SIZE(GET_HEADER(bp)) - DSIZE)

/* adjacent blocks */
#define PRED_FOOTER(bp) ((char *)(bp) - DSIZE)
#define SUCC_HEADER(bp) ((char *)(bp) + GET_SIZE(GET_HEADER(bp)) - WSIZE)
#define PRED_BLK(bp) ((char *)(bp) - GET_SIZE(PRED_FOOTER(bp)))
#define SUCC_BLK(bp) ((char *)(bp) + GET_SIZE(GET_HEADER(bp)))

/* adjacent free blocks in the list */
#define PRED_FREE(bp) (READ((char *)(bp))         == 0? NULL : (int *)((long)(READ((char *)(bp)))         + (long)(heap_ptr)))
#define SUCC_FREE(bp) (READ((char *)(bp) + WSIZE) == 0? NULL : (int *)((long)(READ((char *)(bp) + WSIZE)) + (long)(heap_ptr)))
#define SET_PRED_FREE(bp, val) WRITE((char *)(bp),         (val) == 0? 0 : ((long)val - (long)(heap_ptr)))
#define SET_SUCC_FREE(bp, val) WRITE((char *)(bp) + WSIZE, (val) == 0? 0 : ((long)val - (long)(heap_ptr)))

#define MAX(x, y) ((x) < (y)? (y) : (x))
#define MIN(x, y) ((x) < (y)? (x) : (y))

static char *heap_ptr;
static char *free_blks = NULL;

static void _insert_free_block(void *ptr) {
    if (ptr == NULL) {
        return;
    }
    //dbg_printf("insert free %lld size = %d\n", (long long)ptr, (int)GET_SIZE(GET_HEADER(ptr)));
    if (free_blks == NULL) {
        free_blks = ptr;
        SET_PRED_FREE(ptr, 0);
        SET_SUCC_FREE(ptr, 0);
    } else {
        SET_SUCC_FREE(ptr, free_blks);
        SET_PRED_FREE(free_blks, ptr);
        free_blks = ptr;
        SET_PRED_FREE(ptr, 0);
    }
}

static void _delete_free_block(void *ptr) {
    if (ptr == NULL) {
        return;
    }
    //dbg_printf("delete free %lld size = %d\n", (long long)ptr, (int)GET_SIZE(GET_HEADER(ptr)));
    void *succ_free = SUCC_FREE(ptr);
    //dbg_printf("succ_free = %lld\n", (long long)succ_free);
    if (free_blks == ptr) {
        if (succ_free == NULL) {
            free_blks = NULL;
        } else {
            free_blks = succ_free;
            SET_PRED_FREE(free_blks, 0);
        }
    } else {
        void *pred_free = PRED_FREE(ptr);
    //dbg_printf("pred_free = %lld\n", (long long)pred_free);
        if (succ_free == NULL) {
            SET_SUCC_FREE(pred_free, 0);
        } else {
            SET_SUCC_FREE(pred_free, succ_free);
            SET_PRED_FREE(succ_free, pred_free);
        }
    }
}

static void *_merge_free_blocks(void *ptr) {
    size_t pred_alloc = GET_ALLOC(PRED_FOOTER(ptr));
    size_t succ_alloc = GET_ALLOC(SUCC_HEADER(ptr));
    if (pred_alloc && succ_alloc) {
        /* do nothing */
    } else if (pred_alloc) { //merge with succ
        _delete_free_block(SUCC_BLK(ptr));
        size_t newsize = GET_SIZE(GET_HEADER(ptr)) + GET_SIZE(SUCC_HEADER(ptr));
        WRITE(GET_HEADER(ptr), PACK(newsize, 0));
        WRITE(GET_FOOTER(ptr), PACK(newsize, 0)); //header has changed
    } else if (succ_alloc) {
        _delete_free_block(PRED_BLK(ptr));
        size_t newsize = GET_SIZE(GET_HEADER(ptr)) + GET_SIZE(PRED_FOOTER(ptr));
        WRITE(GET_HEADER(PRED_BLK(ptr)), PACK(newsize, 0));
        WRITE(GET_FOOTER(ptr), PACK(newsize, 0));
        ptr = PRED_BLK(ptr);  //header of ptr isn't changed
    } else {
        _delete_free_block(PRED_BLK(ptr));
        _delete_free_block(SUCC_BLK(ptr));
        size_t newsize = GET_SIZE(GET_HEADER(ptr)) + GET_SIZE(PRED_FOOTER(ptr)) + GET_SIZE(SUCC_HEADER(ptr));
        WRITE(GET_HEADER(PRED_BLK(ptr)), PACK(newsize, 0));
        WRITE(GET_FOOTER(SUCC_BLK(ptr)), PACK(newsize, 0));
        ptr = PRED_BLK(ptr);
    }
    _insert_free_block(ptr);
    return ptr;
}

static void _build(void *ptr, size_t size) {
    if (ptr == NULL) {
        return;
    }
    _delete_free_block(ptr);
    //dbg_printf("build %lld %d\n", (long long)ptr, (int)size);
    size_t blksize = GET_SIZE(GET_HEADER(ptr));
    if (blksize - size > ESIZE) {
        WRITE(GET_HEADER(ptr), PACK(size, 1));
        WRITE(GET_FOOTER(ptr), PACK(size, 1));
        void *split = SUCC_BLK(ptr);
        blksize -= size;
        WRITE(GET_HEADER(split), PACK(blksize, 0));
        WRITE(GET_FOOTER(split), PACK(blksize, 0));
        SET_PRED_FREE(split, 0);
        SET_SUCC_FREE(split, 0);
    //dbg_printf("split merge %lld\n", (long long)split);
        _merge_free_blocks(split);
    } else {
        WRITE(GET_HEADER(ptr), PACK(blksize, 1));
        WRITE(GET_FOOTER(ptr), PACK(blksize, 1));
    }
}

static void *_extend_heap(size_t extend_size) {
    extend_size = (extend_size & 1)? ((extend_size + 1) * WSIZE) : (extend_size * WSIZE);
    char *ptr = mem_sbrk(extend_size);
    if (ptr == (void *)-1) {
        return NULL;
    }
    WRITE(GET_HEADER(ptr), PACK(extend_size, 0));
    WRITE(GET_FOOTER(ptr), PACK(extend_size, 0));
    SET_PRED_FREE(ptr, 0);
    SET_SUCC_FREE(ptr, 0);
    WRITE(GET_HEADER(SUCC_BLK(ptr)), PACK(0, 1));
    return _merge_free_blocks(ptr);
}

static void *_allocate(size_t size) {
    char *best_fit = NULL;
    size_t best_fit_size = 0;
    int fit_cnt = 0;
    for (void* ptr = free_blks; ptr != NULL; ptr = SUCC_FREE(ptr)) {
        size_t now_size = GET_SIZE(GET_HEADER(ptr));
        if (now_size >= size) {
            if (best_fit == NULL || now_size < best_fit_size) {
                best_fit = ptr;
                best_fit_size = now_size;
            }
            if (++fit_cnt == 42) {
                return best_fit;
            }
        }
    }
    if (best_fit != NULL) {
        return best_fit;
    }
    return NULL;
}

int mm_init(void) {
    if ((heap_ptr = mem_sbrk(6 * WSIZE)) == (void *)-1) {
        return -1;
    }
    WRITE(heap_ptr, 0);
    WRITE(heap_ptr + (1 * WSIZE), PACK(ESIZE, 1));
    WRITE(heap_ptr + (2 * WSIZE), 0);
    WRITE(heap_ptr + (3 * WSIZE), 0);
    WRITE(heap_ptr + (4 * WSIZE), PACK(ESIZE, 1));
    WRITE(heap_ptr + (5 * WSIZE), PACK(0, 1));
    heap_ptr += ESIZE;
    free_blks = NULL;
    if (_extend_heap(CHUNKSIZE / WSIZE) == NULL) {
        return -1;
    }
    return 0;
}

void *malloc(size_t size) {
    if (size == 0) {
        return NULL;
    }
    //adjust size, align + header + footer
    size = DSIZE * ((size + DSIZE - 1) / DSIZE + 1);
    //dbg_printf("start malloc %d\n", (int)size);
    char *ptr = _allocate(size);
    if (ptr != NULL) { //find a fit
        _build(ptr, size);
        return ptr;
    } else { //no fit, must extend the heap
        ptr = _extend_heap(MAX(size, CHUNKSIZE) / WSIZE);
        if (ptr == NULL) {
        return NULL;
        }
        _build(ptr, size);
        return ptr;
    }
}

void free(void *ptr) {
    if (ptr == NULL) {
        return;
    }
    size_t size = GET_SIZE(GET_HEADER(ptr));
    WRITE(GET_HEADER(ptr), PACK(size, 0));
    WRITE(GET_FOOTER(ptr), PACK(size, 0));
    SET_PRED_FREE(ptr, 0);
    SET_SUCC_FREE(ptr, 0);
    _merge_free_blocks(ptr);
}

void *realloc(void *oldptr, size_t size) {
    if (size == 0) {
        free(oldptr);
        return 0;
    }
    if(oldptr == NULL) {
        return malloc(size);
    }
    void *newptr = malloc(size);
    size_t oldsize = GET_SIZE(GET_HEADER(oldptr));
    size_t newsize = GET_SIZE(GET_HEADER(newptr));
    size_t cpysize = MIN(oldsize, newsize);
    memcpy(newptr, oldptr, cpysize - DSIZE);
    free(oldptr);
    return newptr;
}

void *calloc (size_t nmemb, size_t size) {
    size_t bytes = nmemb * size;
    void *newptr = malloc(bytes);
    memset(newptr, 0, bytes);
    return newptr;
}

void mm_checkheap(int verbose) {
	/*Get gcc to be quiet. */
	verbose = verbose;
}
