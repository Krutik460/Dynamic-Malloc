# Dynamic-Malloc

In this project I wrote a dynamic storage allocator for C programs, i.e., my
own version of the `malloc`
, 
`free`
, and 
`realloc`
 routines.  You are encouraged to 
explore the design space creatively and implement an allocator 
that is correct, efficient, 
and fast. 
## Description 
Your dynamic storage allocator will consist 
of the following four functions, which are 
declared in 
`mm.h`
 and defined in 
`mm.c`
.   
* `int mm_init(void);`
* `void *mm_malloc(size_t size);`
* `void mm_free(void *ptr);`
* `void *mm_realloc(void *ptr, size_t size);`
The 
`mm.c`
 file we have given you implements a simple memory allocator based on an 
implicit free list, first fit placement, and 
boundary tag coalescing, as described in the 
textbook. Using this as a starting place, modify these functions (and possibly define 
other private 
static
 functions), so that they obey the following semantics:   
* mm_init:Before calling 
`mm_malloc`
, 
`mm_realloc`
, or 
`mm_free`
, the 
application program (i.e., the trace-drive
n driver program that you will use to 
evaluate your implementation) calls 
`mm_init` to perform any necessary 
initializations, such as allocating the initial
 heap area. The return value should be 
−1 if there was a problem in performing the initialization, 0 otherwise.

The driver will call 
mm_init
 before running each trace 
(and after resetting the 
brk
 pointer). Therefore, your 
mm_init 
function should be able to reinitialize 
all state in your allocator each time it is called. In other words, you should not 
assume that it will only be called once. 
* mm_malloc:  The 
`mm_malloc`
 routine returns a pointer
 to an allocated block 
payload of at least 
size
 bytes. The entire allocated block should lie within the 
heap region and should not overlap with
any other allocated chunk. We will 
compare your implementation to the version of 
malloc
supplied in the standard 
C library (
libc
). Since the 
libc
malloc always returns payload pointers that are 
aligned to 8 bytes, your malloc implementation should do likewise and always 
return 8-byte aligned pointers.  
* mm_free:  The 
`mm_free`
 routine frees the block pointed to by 
ptr
It returns 
nothing. This routine is only guaranteed
 to work when the passed pointer (
ptr
) 
was returned by an earlier call to 
`mm_malloc`
or 
`mm_realloc`
 has not yet been 
freed.   
* mm_realloc:  The 
`mm_realloc`
 routine returns a point
er to an allocated 
region of at least 
size 
bytes with the following constraints:   
* if 
`ptr` 
is NULL, the call is equivalent to 
`mm_malloc(size);`  
* if 
`size`
is equal to zero, the call is equivalent to 
`mm_free(ptr);`  
* if 
`ptr`
 is not NULL, it must have been
 returned by an earlier call to 
`mm_malloc`
 or 
`mm_realloc`
.  The call to 
`mm_realloc`
 changes the 
size of the memory block pointed to by 
ptr 
(the 
old block
) to 
size 
bytes and returns the address of the ne
w block. Notice that the address of 
the new block might be the same as th
e old block, or it 
might be different, 
depending on your implementation, the 
amount of internal fragmentation 
in the old block, and the size of the 
realloc
 request.   
The contents of the new block are the same as those of the old 
ptr 
block, 
up to the minimum of the old and 
new sizes. Everything else is 
uninitialized. For example, if the old 
block is 8 bytes and the new block is 
12 bytes, then the first 8 bytes of the 
new block are identical to the first 8 
bytes of the old block and the last 4 
bytes are uninitialized.  Similarly, if 
the old block is 8 bytes and the new block is 4 bytes, then the contents of 
the new block are identical to the first 4 bytes of the old block.   
These semantics must match the 
semantics of the corresponding 
libc malloc
, 
realloc
, and 
free 
routines.  Type 
man malloc 
for complete documentation.
