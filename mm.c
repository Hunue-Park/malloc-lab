/*
 * mm.c - malloc using segregated list
 * KAIST
 * Tony Kim
 * 
 * In this approach, 
 * Every block has a header and a footer 
 * in which header contains reallocation information, size, and allocation info
 * and footer contains size and allocation info.
 * Free list are tagged to the segregated list.
 * Therefore all free block contains pointer to the predecessor and successor.
 * The segregated list headers are organized by 2^k size.
 * 
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"


/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


// My additional Macros
#define WSIZE     4          // word and header/footer size (bytes)
#define DSIZE     8          // double word size (bytes)
#define INITCHUNKSIZE (1<<6)
#define CHUNKSIZE (1<<12)//+(1<<7) 

#define LISTLIMIT     20      
#define REALLOC_BUFFER  (1<<7)    

#define MAX(x, y) ((x) > (y) ? (x) : (y)) 
#define MIN(x, y) ((x) < (y) ? (x) : (y)) 

// Pack a size and allocated bit into a word
#define PACK(size, alloc) ((size) | (alloc))

// Read and write a word at address p 
#define GET(p)            (*(unsigned int *)(p))
// 포인터 p의 주소값이 가리키는 메모리에 들어있는 값(주로 헤더정보)를 가져오는 매크로
#define PUT(p, val)       (*(unsigned int *)(p) = (val) | GET_TAG(p))
// p 메모리에 val 와 get_tag 의 값을 넣는 매크로, 여기서 get tag 는 re_allocation 여부를 담고있다.
#define PUT_NOTAG(p, val) (*(unsigned int *)(p) = (val))
// get tag 없이 val 만 p 에 넣는 매크로

// Store predecessor or successor pointer for free blocks 
#define SET_PTR(p, ptr) (*(unsigned int *)(p) = (unsigned int)(ptr))
// ptr 포인터를 p 포인터가 가리키는 메모리에 넣는 매크로

// Read the size and allocation bit from address p 
#define GET_SIZE(p)  (GET(p) & ~0x7)
// original get_size와 동일  
#define GET_ALLOC(p) (GET(p) & 0x1)
// original get_alloc 과 동일
#define GET_TAG(p)   (GET(p) & 0x2)
// re-allocation 여부를 알려줌. 1=> RA 되어있음
#define SET_RATAG(p)   (GET(p) |= 0x2)
// RA tag를 부여하는 매크로. 
// 아 그러면 여기서 re alloc 의 의미는 realloc 이 가능한 블럭이라는걸 알려주는 flag??
#define REMOVE_RATAG(p) (GET(p) &= ~0x2)
// RA tag를 제거하느 매크로

// Address of block's header and footer 
#define HDRP(ptr) ((char *)(ptr) - WSIZE)
#define FTRP(ptr) ((char *)(ptr) + GET_SIZE(HDRP(ptr)) - DSIZE)
// 원본 hdrp ftrp 와 동일 //

// Address of (physically) next and previous blocks 
#define NEXT_BLKP(ptr) ((char *)(ptr) + GET_SIZE((char *)(ptr) - WSIZE))
#define PREV_BLKP(ptr) ((char *)(ptr) - GET_SIZE((char *)(ptr) - DSIZE))
// 원본 boundary tag check 매크로와 동일. //

// Address of free block's predecessor and successor entries 
#define PRED_PTR(ptr) ((char *)(ptr))
#define SUCC_PTR(ptr) ((char *)(ptr) + WSIZE)
// header 포인터를 설정해주는것과 비슷하게 블럭의 ptr 을 집어넣으면 pred_ptr & succ_ptr 을 반환해준다. //

// Address of free block's predecessor and successor on the segregated list 
#define PRED(ptr) (*(char **)(ptr))   // *(char **)(ptr)
#define SUCC(ptr) (*(char **)(SUCC_PTR(ptr)))
// pred 와 succ 포인터를 모아놓은 segregated list 에 접근하고 해당 포인터가 가리키는 값으로 이동하기 위해선
// 이중 포인터가 필요. 

// End of my additional macros


// Global var
void *segregated_free_lists[LISTLIMIT]; 
// free blocks 를 모아놓는 segregated free list 선언. Q. 최초 제한은 왜 20으로 두는걸까 -> 2^20 이면 충분할걸?

// Functions
static void *extend_heap(size_t size);
static void *coalesce(void *ptr);
static void *place(void *ptr, size_t asize);
static void insert_node(void *ptr, size_t size);
static void delete_node(void *ptr);

//static void checkheap(int verbose);


///////////////////////////////// Block information /////////////////////////////////////////////////////////
/*

 
A   : Allocated? (1: true, 0:false)
RA  : Reallocation tag (1: true, 0:false)
 
 < Allocated Block >
 
 
             31 30 29 28 27 26 25 24 23 22 21 20 19 18 17 16 15 14 13 12 11 10  9  8  7  6  5  4  3  2  1  0
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 Header :   |                              size of the block                                       |  |  | A|
    bp ---> +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
            |                                                                                               |
            |                                                                                               |
            .                              Payload and padding                                              .
            .                                                                                               .
            .                                                                                               .
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 Footer :   |                              size of the block                                       |     | A|
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 
 
 < Free block >
 
             31 30 29 28 27 26 25 24 23 22 21 20 19 18 17 16 15 14 13 12 11 10  9  8  7  6  5  4  3  2  1  0
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 Header :   |                              size of the block                                       |  |RA| A|
    bp ---> +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
            |                        pointer to its predecessor in Segregated list                          |
bp+WSIZE--> +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
            |                        pointer to its successor in Segregated list                            |
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
            .                                                                                               .
            .                                                                                               .
            .                                                                                               .
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 Footer :   |                              size of the block                                       |     | A|
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+

 
 
*/
///////////////////////////////// End of Block information /////////////////////////////////////////////////////////

team_t team = {
    /* Team name */
    "one team",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};



//////////////////////////////////////// Helper functions //////////////////////////////////////////////////////////
static void *extend_heap(size_t size)
{
    void *ptr;                   
    size_t asize;                // Adjusted size 
    
    asize = ALIGN(size);
    
    if ((ptr = mem_sbrk(asize)) == (void *)-1)
        return NULL;
    
    // Set headers and footer 
    PUT_NOTAG(HDRP(ptr), PACK(asize, 0));  
    PUT_NOTAG(FTRP(ptr), PACK(asize, 0));   
    PUT_NOTAG(HDRP(NEXT_BLKP(ptr)), PACK(0, 1)); 
    insert_node(ptr, asize);
    // 새로 확장한 메모리의 포인터와 크기를 insert node함수에 넣는다. 

    return coalesce(ptr);
}

static void insert_node(void *ptr, size_t size) {
    int list = 0;
    void *search_ptr = ptr;
    // 넣고자 하는 free block 의 bp 를 search ptr 로 선언 
    void *insert_ptr = NULL;
    
    // Select segregated list 
    while ((list < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        // 2^k 크기로 segregated 가 분류되어있으므로 1 비트 내릴때마다 2^k-1 되는것
        list++;
        // 몇 번째 리스트인지 알려주는 변수
    }
    
    // Keep size ascending order and search
    search_ptr = segregated_free_lists[list];
    // list 번째 segregated free list 에 있는 첫번째 free block 을 가리키는 포인터로 
    // search ptr 을 갱신
    while ((search_ptr != NULL) && (size > GET_SIZE(HDRP(search_ptr)))) {
        insert_ptr = search_ptr;
        search_ptr = PRED(search_ptr);
        // 해당 search ptr 가 가리키는 free block 보다 이전의 free block 으로 
        // search ptr 를 갱신
    }
    
    // Set predecessor and successor 
    if (search_ptr != NULL) {
        if (insert_ptr != NULL) {
            SET_PTR(PRED_PTR(ptr), search_ptr);
            SET_PTR(SUCC_PTR(search_ptr), ptr);
            SET_PTR(SUCC_PTR(ptr), insert_ptr);
            SET_PTR(PRED_PTR(insert_ptr), ptr);
        } else {
            SET_PTR(PRED_PTR(ptr), search_ptr);
            SET_PTR(SUCC_PTR(search_ptr), ptr);
            SET_PTR(SUCC_PTR(ptr), NULL);
            segregated_free_lists[list] = ptr;
        } //// 굿노트 그림참조. 
    } else { // 해당 segregated free list[list] 가 비어있는거나 마찬가지 일땐
        if (insert_ptr != NULL) {
            SET_PTR(PRED_PTR(ptr), NULL);
            SET_PTR(SUCC_PTR(ptr), insert_ptr);
            SET_PTR(PRED_PTR(insert_ptr), ptr);
        } else {
            SET_PTR(PRED_PTR(ptr), NULL);
            SET_PTR(SUCC_PTR(ptr), NULL);
            segregated_free_lists[list] = ptr;
        }
    }
    
    return;
}


static void delete_node(void *ptr) {
    int list = 0;
    size_t size = GET_SIZE(HDRP(ptr));
    
    // Select segregated list 
    while ((list < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        list++;
    }
    
    if (PRED(ptr) != NULL) { 
    // ptr 블럭보다 사이즈가 큰 블럭이 segregated free list[list]에 존재할때
        if (SUCC(ptr) != NULL) {
        // ptr 블럭보다 사이즈가 작은 블럭이 존재한다면  
            SET_PTR(SUCC_PTR(PRED(ptr)), SUCC(ptr));
            SET_PTR(PRED_PTR(SUCC(ptr)), PRED(ptr));
        } else {
            SET_PTR(SUCC_PTR(PRED(ptr)), NULL);
            segregated_free_lists[list] = PRED(ptr);
        } /// 굿노트 참조
    } else {
        if (SUCC(ptr) != NULL) {
            SET_PTR(PRED_PTR(SUCC(ptr)), NULL);
        } else {
            segregated_free_lists[list] = NULL;
        }
    }
    
    return;
}


static void *coalesce(void *ptr)
{
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(ptr)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t size = GET_SIZE(HDRP(ptr));
    

    // Do not coalesce with previous block if the previous block is tagged with Reallocation tag
    // if (GET_TAG(HDRP(PREV_BLKP(ptr))))
    //     prev_alloc = 1;
        // 이전 블록이 re alloc 되어있으면 coalesce 하지말것. 
        // 왜냐하면 re alloc 이면 그 블럭은 나중에 re alloc 할때 buffer 고려해서 
        // re alloc 할때 쓸 수도 있으니까. 

    if (prev_alloc && next_alloc) {                         // Case 1
        return ptr;
    }
    else if (prev_alloc && !next_alloc) {                   // Case 2
        delete_node(ptr);
        delete_node(NEXT_BLKP(ptr));
        // 원래 있던 next free block 과 새로 생기는 free block 을 segregated free list 에서 삭제
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        PUT_NOTAG(HDRP(ptr), PACK(size, 0));
        PUT_NOTAG(FTRP(ptr), PACK(size, 0));
        // 여기서 put 은 ra_tag 를 붙이는 put 이다. 
    } else if (!prev_alloc && next_alloc) {                 // Case 3 
        delete_node(ptr);
        delete_node(PREV_BLKP(ptr));
        size += GET_SIZE(HDRP(PREV_BLKP(ptr)));
        PUT_NOTAG(FTRP(ptr), PACK(size, 0));
        PUT_NOTAG(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    } else {                                                // Case 4
        delete_node(ptr);
        delete_node(PREV_BLKP(ptr));
        delete_node(NEXT_BLKP(ptr));
        size += GET_SIZE(HDRP(PREV_BLKP(ptr))) + GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        PUT_NOTAG(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        PUT_NOTAG(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    }
    
    insert_node(ptr, size);
    // 최종적으로 만들어진 free block 의 포인터와 사이즈를 segregated free list 에 삽입
    
    return ptr;
}

static void *place(void *ptr, size_t asize)
{
    size_t ptr_size = GET_SIZE(HDRP(ptr));
    // ptr size 는 해당 ptr 가 가리키는 free block 전체의 사이즈 
    size_t remainder = ptr_size - asize;
    // asize 는 새로 할당하는 block 전체의 사이즈
    
    delete_node(ptr);
    // place 는 할당하는 과정이니 해당 블럭을 s_free list 에서 삭제해야함 
    
    
    if (remainder <= DSIZE * 2) { 
    // minimum free block 이 2 * DSIZE 만큼의 크기를 가지므로
    // header + prev_ptr + succ_ptr + footer => 4 words 
        // Do not split block 
        PUT_NOTAG(HDRP(ptr), PACK(ptr_size, 1)); 
        // 얘네는 notag로 바꿔도 문제 없음. 
        PUT_NOTAG(FTRP(ptr), PACK(ptr_size, 1)); 
        // 어쨌든 이 allocated block 이 나중에 free block 으로 바뀌었을때 최소 5word의 크기를
        // 가지는 거니까 re allocation 에 쓸수도 있다. 
    }
    
    else if (asize >= 73) {
        // Split block
        PUT_NOTAG(HDRP(ptr), PACK(remainder, 0));
        // 여기서 생기는 remainder free block 은 사이즈가 꽤 커서 나중에 re allocation 할때 
        // 쓸수도 있으니까 ra tag 를 붙여서 남겨놓는다. 
        PUT_NOTAG(FTRP(ptr), PACK(remainder, 0));
        // pack 에 들어가는 size는 binary 다 
        PUT_NOTAG(HDRP(NEXT_BLKP(ptr)), PACK(asize, 1));
        // RA tag 없이 allocation 하기만 하면 됨. 
        PUT_NOTAG(FTRP(NEXT_BLKP(ptr)), PACK(asize, 1));
        insert_node(ptr, remainder);
        // remainder 만큼의 사이즈를 가지는 free block 이 생긴거니까 
        // S_free list 에 insert 한다. 
        return NEXT_BLKP(ptr);
        
    }
    
    else { // 이 else 는 asize >= 100 이지만 reaminder < 4 word 인 경우다. 
        // 그래서 어차피 이 remainder 는 남겨봤자 re allocation 할때 못쓰니까 put no tag 임. 
        // Split block
        PUT_NOTAG(HDRP(ptr), PACK(asize, 1)); 
        PUT_NOTAG(FTRP(ptr), PACK(asize, 1)); 
        PUT_NOTAG(HDRP(NEXT_BLKP(ptr)), PACK(remainder, 0)); 
        PUT_NOTAG(FTRP(NEXT_BLKP(ptr)), PACK(remainder, 0)); 
        // 왜 이 remainder에는 ra tag 를 안붙이고 free 로 split 하는 걸까 
        insert_node(NEXT_BLKP(ptr), remainder);
    }
    return ptr;
} // 왜 place 함수에는 싹다 no tag 로 붙여도 되는걸까 



//////////////////////////////////////// End of Helper functions ////////////////////////////////////////






/*
 * mm_init - initialize the malloc package.
 * Before calling mm_malloc, mm_realloc, or mm_free, 
 * the application program calls mm_init to perform any necessary initializations,
 * such as allocating the initial heap area.
 *
 * Return value : -1 if there was a problem, 0 otherwise.
 */
int mm_init(void)
{
    int list;         
    char *heap_start; // Pointer to beginning of heap
    
    // Initialize segregated free lists
    for (list = 0; list < LISTLIMIT; list++) {
        segregated_free_lists[list] = NULL;
    }
    
    // Allocate memory for the initial empty heap 
    if ((long)(heap_start = mem_sbrk(4 * WSIZE)) == -1)
        return -1;
    
    PUT_NOTAG(heap_start, 0);                            /* Alignment padding */
    PUT_NOTAG(heap_start + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT_NOTAG(heap_start + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT_NOTAG(heap_start + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
    
    if (extend_heap(INITCHUNKSIZE) == NULL)
        return -1;
    
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 *
 * Role : 
 * 1. The mm_malloc routine returns a pointer to an allocated block payload.
 * 2. The entire allocated block should lie within the heap region.
 * 3. The entire allocated block should overlap with any other chunk.
 * 
 * Return value : Always return the payload pointers that are alligned to 8 bytes.
 */
void *mm_malloc(size_t size)
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    void *ptr = NULL;  /* Pointer */
    
    // Ignore size 0 cases
    if (size == 0)
        return NULL;
    
    // Align block size
    if (size <= DSIZE) {
        asize = 2 * DSIZE;
    } else {
        asize = ALIGN(size+DSIZE);
    }
    // size 는 malloc 을 할당하고 싶은 사이즈. 
    // asize 는 실제로 heap 에 할당되는 사이즈. header + payload + footer
    int list = 0; 
    size_t searchsize = asize;
    // Search for free block in segregated list
    while (list < LISTLIMIT) {
        if ((list == LISTLIMIT - 1) || ((searchsize <= 1) && (segregated_free_lists[list] != NULL))) {
            ptr = segregated_free_lists[list];
            // Ignore blocks that are too small or marked with the reallocation bit
            while ((ptr != NULL) && ((asize > GET_SIZE(HDRP(ptr))) ))
            // 여기서 get tag 가 RA 여부를 알려주는 매크로. 
            // 즉 앞 조건을 만족하거나 해당 free block 의 RA tag 가 1 이면 지나간다 왜?
            {
                ptr = PRED(ptr);
                // 좀 더 큰 free block 을 향해서 포인터 이동. in segregated free list. 
            }
            if (ptr != NULL)
                break;
        }
        
        searchsize >>= 1;
        list++;
    }
    
    // if free block is not found, extend the heap
    if (ptr == NULL) {
        extendsize = MAX(asize, CHUNKSIZE);
        
        if ((ptr = extend_heap(extendsize)) == NULL)
            return NULL;
    }
    
    // Place and divide block
    ptr = place(ptr, asize);
    
    
    // Return pointer to newly allocated block 
    return ptr;
}

/*
 * mm_free - Freeing a block does nothing.
 *
 * Role : The mm_free routine frees the block pointed to by ptr
 *
 * Return value : returns nothing
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
 
    // REMOVE_RATAG(HDRP(NEXT_BLKP(ptr)));
    // next block 의 header 에 들어있는 RA tag 를 없애준다. 
    PUT_NOTAG(HDRP(ptr), PACK(size, 0));
    PUT_NOTAG(FTRP(ptr), PACK(size, 0));
    // 새로 만들어지는 free block 에는 RA tag 붙임. 
    
    insert_node(ptr, size);
    // free 했으니까 S_free list 에 삽입해야지. 
    coalesce(ptr);
    
    return;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 *
 * Role : The mm_realloc routine returns a pointer to an allocated 
 *        region of at least size bytes with constraints.
 *
 *  I used https://github.com/htian/malloc-lab/blob/master/mm.c source idea to maximize utilization
 *  by using reallocation tags
 *  in reallocation cases (realloc-bal.rep, realloc2-bal.rep)
 *  reallocation tag가 필요한 경우는 언제일까?? 
 *  allocated block 바로 다음에 나오는 free block 에 reallocation tag가 필요하다. 
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *new_ptr = ptr;    /* Pointer to be returned */
    size_t new_size = size; /* Size of new block */
    int remainder;          /* Adequacy of block sizes */
    int extendsize;         /* Size of heap extension */
    int block_buffer;       /* Size of block buffer */
    
    // Ignore size 0 cases
    if (size == 0)
        return NULL;
    
    // Align block size
    if (new_size <= DSIZE) {
        new_size = 2 * DSIZE;
    } else {
        new_size = ALIGN(size+DSIZE);
    }
    
    /* Add overhead requirements to block size */
    new_size += REALLOC_BUFFER;
    // realloc buffer 는 2^7 의 값을 가진다. 
    
    /* Calculate block buffer */
    block_buffer = GET_SIZE(HDRP(ptr)) - new_size;
    
    /* Allocate more space if overhead falls below the minimum */
    if (block_buffer < 0) {
        /* Check if next block is a free block or the epilogue block */
        if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr))) || !GET_SIZE(HDRP(NEXT_BLKP(ptr)))) {
            remainder = GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLKP(ptr))) - new_size;
            if (remainder < 0) {
                extendsize = MAX(-remainder, CHUNKSIZE);
                if (extend_heap(extendsize) == NULL)
                    return NULL;
                remainder += extendsize;
            }
            
            delete_node(NEXT_BLKP(ptr));
            
            // Do not split block
            PUT_NOTAG(HDRP(ptr), PACK(new_size + remainder, 1)); 
            PUT_NOTAG(FTRP(ptr), PACK(new_size + remainder, 1)); 
        } else {
            new_ptr = mm_malloc(new_size - DSIZE);
            memcpy(new_ptr, ptr, MIN(size, new_size));
            mm_free(ptr);
        }
        block_buffer = GET_SIZE(HDRP(new_ptr)) - new_size;
    }
    
    // Tag the next block if block overhead drops below twice the overhead 
    // if (block_buffer < 2 * REALLOC_BUFFER)
    //     SET_RATAG(HDRP(NEXT_BLKP(new_ptr)));
    
    // Return the reallocated block 
    return new_ptr;
}