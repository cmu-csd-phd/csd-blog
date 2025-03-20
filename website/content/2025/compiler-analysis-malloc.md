+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "Compiler-Assisted Malloc for Automatically Reducing Data Movement"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2025-03-18

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Systems"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
# Consider these similar to keywords specified for a research paper.
tags = ["memory-allocation", "compiler-analysis"]

[extra]
author = {name = "Valerie Choung", url = "https://nicebowlofsoup.com" }
# The committee specification is  a list of objects similar to the author.
committee = [
    {name = "Todd Mowry", url = "https://toddcmowry.org"},
    {name = "Dimitrios Skarlatos", url = "https://cs.cmu.edu/~dskarlat/"},
    {name = "Benjamin Stoler", url = "https://benstoler.com"}
]

+++

In this post, I'll be discussing my part of my work on how to use compiler 
analysis to aid in optimizing memory allocation. 
I will begin with some background and motivation, and then introduce my 
proposed workflow as well as some interesting 
challenges that this work involves.

# Memory Bottlenecks and Data Movement

CPU speeds used to be the main bottleneck in applications, but over time, 
CPUs have gotten faster and faster. Along with the rise of big data, 
applications’ use of large datasets and consequent memory needs have become 
increasingly pronounced. As a result, bottlenecks have shifted away from CPU 
computation speeds and instead towards memory speeds. Modern applications are 
therefore less _compute-bound_ and more _memory-bound_.

Not all memory-bound applications, however, have the same flavor of memory 
demands - some may benefit more from better memory latency, and others may 
benefit more from better memory bandwidth or larger capacity.

Memory latency is usually a problem when memory takes a long time to retrieve 
a piece of data and provide the data to the requester. Generally, memory that 
has high capacity and memory that is physically far from the compute core will 
have higher latency. In a traditional memory architecture, this is addressed 
by placing small, fast caches next to CPUs, in hopes that a data fetch request 
would be handled by the cache, rather than slow main memory.

> **_Detour_: Basic Ideas of Caches**
> </br></br>
> A cache has relatively small capacity, but it can serve requests 
for data very quickly if the data is present in the cache. If the requested 
data is not in the cache, the request must be served by slower main memory. 
An application can make effective use of a cache by having a small set of 
very frequently used data. Ideally, that set of data would stay cached.  
> For a hardware cache, data is usually moved into or out of the cache in 
fixed-size chunks, called _cache lines_. For example, if a cache line is 64 
bytes, and an application requests 8 bytes of data at address `0xB0BACAFE`, all 
64 bytes of data from `0xB0BACAC0` to `0xB0BACB00` would be moved into the cache. 
> If the cache is already full, then a cached line would have to be 
> _evicted_ for a new line to be cached. 
> ![Cache Lines](cache-line.png)
> Hot-cold separation in caches is a concept that helps “hot” (frequently 
used) data stay in the cache, while making it likely that “cold” 
(infrequently used) data would not stay in the cache for long: 
Hot data should be stored separately from cold data, 
so that it is unlikely that a single cache line holds both hot and cold data. 
If a cache line has a mix of hot and cold data, then having both types of 
data will “waste” some cache space. If we already have a cached line of hot 
and cold data and we wish to evict the cold data from the cache, then the 
hot data would be evicted alongside the cold data. This is unideal because 
when the hot data is later accessed again, we would need to move the line 
of data back into the cache, increasing data movement.
<p></p>
</br>

![Memory Hierarchy Diagram](mem_hierarchy.png)

Memory bandwidth is a problem when memory cannot handle the volume of requests. 
This easily occurs when memory access patterns are highly irregular, since 
the requested data is rarely cached, causing nearly every request to go to 
main memory (which usually has insufficient bandwidth.)

Ultimately, the core problem behind _both_ types of memory bottlenecks is, more broadly, 
data movement. There is an inherent cost to data movement, whether it be the data 
movement between disk and main memory, between main memory 
and caches, or even between different caches. 
To add to it, data movement negatively impacts not only performance, but also
 energy costs as well.
As it turns out, we can reduce data 
movement with careful _data placement_. 


# Key Concepts for Data Placement

Data placement is a hard problem that can be solved on a few levels: 
Should a data object go onto one memory node or another? What if memory 
nodes have different types of hardware memory with different tradeoffs 
(e.g. one type may have better bandwidth but worse latency)? 
Can data objects be arranged to improve the effect of prefetching and make
better use of caches? 

Generally, optimizing data placement is either in form of:

1. **Tailored Programming**: Application programmer analyzes the application’s 
memory accesses, and either arranges data objects in a certain way or rewrites 
the calculations to make better use of existing data objects’ layouts. 
(Example: [Compressing matrices or changing order of operations for matrix transformations](https://people.eecs.berkeley.edu/~demmel/cs267_Spr99/Lectures/Lect_02_1999b.pdf)), or

2. **One-Size-Fits-All**: The programmer uses pre-optimized data structures. 
For example, a Python programmer can use libraries with optimized hash tables. 
Whoever implemented the libraries is hoping that the programmer will use the data 
structures in a predictable/canonical way. 

Much like with clothes shopping, the tailored version performs better but 
requires high (human) overhead, while the one-size-fits-all version fits almost 
nobody quite right.

Some key concepts for data placement include:
- Some memory nodes may be closer to compute nodes and therefore faster to access
- Memory nodes may have different bandwidth/latency/capacity capabilities
- Some data objects might stay cached, and thus the particular main memory node 
that it is allocated on would matter far less

For the rest of this blog, we'll mostly focus on optimizing data placement for 
cache utility, although I do have a related project that focuses on
allocations across different types of hardware memory nodes. (Feel free to 
[shoot me an email](mailto://soup[at]cmu.edu) for more information about either project!)

# Memory Allocation (``malloc``)
There is actually a lot of potential for memory allocation schemes to influence 
data placement! Unfortunately, the “default” Glibc malloc is basically archaic 
and doesn’t try to do much with data placement. It was designed with the premise 
that “if `malloc` runs faster (returns quickly), then the overall program runs faster.” 
This made sense in the 1970s when almost everything was CPU-bound, but nowadays 
this is a very outdated and simplistic idea.

There have been several efforts to optimize data placement through malloc implementations. 
On one hand, custom memory allocators like the 
[JVM custom allocator](https://help.salesforce.com/s/articleView?id=001118058&type=1) 
and the [Intel TBB allocator](https://www.bsdforge.com/docs/sharedocs/tbb/a00551.html) 
are so finely tuned to their intended applications to the point that trying to 
re-use these allocators for _other_ applications would be unlikely to succeed.
On the other hand, modern general-purpose memory allocators such as 
[mimalloc](https://github.com/microsoft/mimalloc) have moved away from that 
notion and now include optimizations like [sharding malloc's internal bookkeeping 
structures](https://www.microsoft.com/en-us/research/uploads/prod/2019/06/mimalloc-tr-v1.pdf), 
which helps for multi-threaded applications with shared states. These optimizations 
are designed in anticipation of potential applications that will be ran.

But what if the memory allocator could receive actual information about the application's 
behavior and characteristics _before_ it is even ran? This leads us to the idea of 
tweaking the compilation pipeline to pass information from the compiler to 
the memory allocator.

# Tweaking the Compilation Pipeline
As shown below, the typical compilation pipeline involves turning source code into 
application executables, and then linking to relevant libraries.

![Compiler (Unmodded)](cama-nomods.png)

The compiler’s role is to convert source code into Intermediate Representation (IR) 
(which you can think of as a language “between” source code and assembly), run 
analysis passes on the IR, run transformation passes on the IR, and then convert it into 
assembly/binary. Analysis passes do things like identifying dependencies between variables, 
whereas transformation passes usually perform compiler optimizations (such as 
[loop unrolling](https://www.d.umn.edu/~gshute/arch/loop-unrolling.html)) 
while making use of analysis results. 

![Basic Compilation Steps](compiler-passes.png)

The idea in my research is that we don’t need to throw away compiler analysis results 
by the end of compilation. Compiler analysis results can be useful not only in 
compiler optimizations, but also in optimizations outside of the compiler. In 
our case, we want `malloc` to use compiler analysis results.

![Compiler (Modded)](cama-mods.png)

In my approach, I introduce a new analysis pass that analyzes the memory access 
patterns in the application. The results of the analysis are embedded into the 
final application executable, and a library (e.g. the `malloc` library) would 
be able to access the analysis results and react accordingly. In the context of 
memory allocation, I provide an implementation of `malloc` that reads the results 
from the analysis pass and then decides where to place data objects based on 
those results.

One of the advantages of this approach is that this requires no change to the 
application source code. After all, the `malloc` interface 
(i.e. ``malloc``/`free`/`realloc`/`calloc`) can be wholly unchanged. The application 
would only need to be re-compiled and re-linked to take advantage of this approach.

This is also language-agnostic: as long as the compiler is able to convert the 
source code language into IR, the analysis pass can be applied. 

# Improving Cache Performance through Memory Allocation

The goal is to arrange data objects next to each other so that the objects 
are likely to share cache lines. If arranged carefully, fetching one data 
object would implicitly “prefetch” other data objects. But how do we decide 
which data objects should be next to each other?

The answer to this is by using _co-access sets_, or _csets_. 
Csets are sets of objects that are frequently accessed together, or within 
narrow time frames. For example, in the following pseudocode snippet, 
objects 1, 2, and 3 would be in a co-access set since they are accessed together.

```c
fn sample():
	int *object_1 = malloc(sizeof(int) * 100);
	int *object_2 = malloc(sizeof(int) * 100);
	int *object_3 = malloc(sizeof(int) * 100);

	...

	for i in range(100):
		object_1[i] = object_2[i] + object_3[i];
```
If we used standard Glibc `malloc`, then each of the three objects would simply 
be placed somewhere in memory with sufficient space. On the other hand, given 
knowledge that the three objects share a cset, a cset-aware malloc implementation 
can make an attempt to put the three objects next to each other.

But what if objects in a cset are too large to fit in a cache line? Well, 
we would still have hot-cold separation in the cache, since parts of different 
objects can still share a cache line and help decrease data movement.

## Identifying Csets
Conveniently, the compiler's view of an application is much like a control 
flow graph (CFG) with instructions in each basic block:

![Basic CFG with Instructions](cfg-instrs.png)

Based on this CFG with instructions, we can create a CFG where each block 
continas a sequence of accessed variables instead, like such: 

![Basic CFG with Variable/Mem Accesses](cfg-accesses.png)

Now, we identify co-access _pairs_ of variables, using a sliding window technique 
along control flow paths. In the above example, regardless of which branch is taken, 
variables x and y are always accessed in immediate succession. So, variables x and 
y would be a clear example of a co-access pair. Each co-access pair will have a 
rank that describes how strong the co-access is.

Once multiple co-access pairs have been identified, we use 
[Union-Find](https://www.cs.cmu.edu/~15451-f15/lectures/lect0914.pdf) 
to form groups of co-access pairs. These groups are then used as csets. The cset 
analysis pass will then tag the calls to `malloc` with a cset ID for calls to `malloc` 
that produce variables belonging to the same cset. 

## Implementing Cset-aware Malloc

When `malloc` is called, it will check if the current call to `malloc` has a tag 
for the cset ID from the analysis pass. If the cset ID has not been seen before, 
`malloc` will reserve a small pool of memory for objects in that cset. In the 
case where the cset ID has been seen before, then `malloc` will check if any 
reserved pools of memory for that cset have sufficient space for the current 
object for which we need to allocate memory. If so, then the object will be placed 
in the reserved pool. Otherwise, a new pool of memory will be reserved for the same cset.

The size of a memory pool starts out fairly small, but as more memory pools for 
the same cset are being reserved, the sizes scale. This way, when an object is being 
created but does not fit into an existing pool, a new pool is reserved with a size 
twice that of the previously reserved pool (for the same cset).

In the below example, we consider a dictionary implemented by a linked list, 
where the nodes’ values are pointers to separately allocated objects:

```c
struct list_node {
    struct list_node *next;
    int key;
    char *value;
}

list_node *n_1 = malloc(sizeof(list_node));
n_1->next = NULL;
n_1->key = 0;
n_1->value = malloc(1000);
...

def find(int key) {
    for (list_node *cur = n_1; cur != NULL; cur = cur->next) {
        if (cur->key == key) {
            return cur->value;
        }
    }
    return None;
}
```
If a `dict.find`
 function is implemented by just stepping through the linked list until a matching key 
is found, then it is likely that the nodes themselves would form a cset, and the 
values themselves would form a separate cset:

![Linked List Dictionary example of Csets in Action](linked-list-csets.png)

# Conclusions and Future Directions
Using compiler analysis in conjunction with a special `malloc` implementation is 
an extremely easy way to optimize an application with minimal invasiveness. So far,
we've achieved performance on par or better than standard Glibc `malloc` on small 
test applications.
There is still plenty of room for improvement, as well as interesting design decisions 
still under experimentation:
- When using the sliding window to identify co-access pairs, the size of the window 
becomes very important. On one hand when the window size is smaller, the level of 
co-access needed to form a pair is much higher. On the other hand, if the window size 
is too large, the co-accesses will be weaker, and the analysis will become much 
slower due to [path explosion](https://en.wikipedia.org/wiki/Path_explosion).
- The use of co-access pairs' ranks to form csets can result in some interesting 
scenarios. For example, consider the scenario when Object A and Object B form a 
co-access pair, and Object B and Object C form a co-access pair, but Object A 
and Object C do _not_ form a co-access pair. Then based on the ranks of both pairs, 
we would need to determine whether all three objects should belong in the same 
cset, or if one of the objects should be left out of the cset.
- Branches in control flow should be taken into consideration when ranking co-access
pairs as well.
![CFG with Branching Problem](branching-problem.png)
In this example CFG, if the branch on the right is always taken, then x and y should
clearly still be a co-access pair. However, if the branch on the left is always taken, 
then x and y would be a much weaker co-access pair, if at all. The solution to this 
problem is to _weight_ the branches or paths according to the probability that they 
would be chosen. However, statically determining these likelihoods is not at all 
easy. There are a number of [branch predictors and speculation techniques](https://course.ece.cmu.edu/~ece740/f13/lib/exe/fetch.php?media=onur-740-fall13-module7.4.1-branch-prediction.pdf) 
that try to address this problem both statically and at runtime.
- Handling multi-threaded applications requires a bit more analysis. It could be 
unideal to pool together co-access sets if the sets' data objects are in high 
contention across multiple threads - pooling could increase [false sharing](https://en.wikipedia.org/wiki/False_sharing) 
and degrade performance.

# Relevant Links
- [LLAMA - Automatic Memory Allocations](https://github.com/derrickgreenspan/LLAMA)
- [Affinity Alloc](https://www.cs.cmu.edu/~beckmann/publications/papers/2023.micro.affinity.pdf)

<style>
img[alt="Compiler (Modded)"], img[alt="Compiler (Unmodded)"] {
width: calc(50% - 2rem)
}

img[alt="Memory Hierarchy Diagram"] {
width: calc(80%)
}

img[alt="Cache Lines"] {
width: calc(95%)
}

img[alt~="CFG"] {
width: calc(75%)
}

</style>

