+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "Breaking Through the Memory Wall of Transactional Database Systems with Processing-in-Memory"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2025-11-01

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Systems"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
# Consider these similar to keywords specified for a research paper.
tags = ["database systems", "novel hardware", "transaction processing"]

[extra]
author = {name = "Hyoungjoo Kim", url = "https://hyoungjook.github.io/" }
# The committee specification is  a list of objects similar to the author.
committee = [
    {name = "Todd C. Mowry", url = "https://www.toddcmowry.org/"},
    {name = "George Amvrosiadis", url = "https://users.ece.cmu.edu/~gamvrosi/"},
    {name = "William Zhang", url = "https://17zhangw.github.io/"},
]
+++

Modern computer systems are fast—until they are not. 
The memory channel bandwidth between DRAM and the CPU has been far behind the CPU performance for more than three decades, and the gap between their performances (called [the Memory Wall](https://dl.acm.org/doi/pdf/10.1145/216585.216588)) is larger than ever nowadays. 
This has become a serious problem today since the most important workloads (e.g., databases, AI, graph analytics, genomics, etc.) are data-intensive, making their performance bottlenecked by the memory speed.
Computer architects bridge this gap by keeping hot data in a fast, small SRAM cache in the CPU. 
This allows serving the CPU's memory requests from the on-chip cache, avoiding sending them to DRAM over the slow off-chip memory channel. 
However, due to the limited capacity of SRAM-based cache, most of the memory requests eventually go to DRAM if the cache capacity cannot accommodate all the hot data. 
As a result, memory-intensive applications with a working set larger than a few GBs suffer from a performance bottleneck due to the slow off-chip memory channel.

Online Transaction Processing (OLTP) workloads are no exception. 
Lying at the heart of many business applications, including banking, e-commerce, and logistics, the goal of OLTP is to process transactions on the underlying database with high throughput while maintaining its integrity. 
A transactional database management system (DBMS) is designed to execute the OLTP workloads efficiently.
It uses _indexes_ (implemented with B+ trees) to quickly locate the _tuples_ requested by the client and [_version chains_](https://www.vldb.org/pvldb/vol10/p781-Wu.pdf) to resolve conflicts between concurrent requests from multiple clients.
Since an OLTP workload has a working set of an indefinite size, most data access requests end up going to DRAM and are served through the slow memory channel. 
Hence, the transaction throughput of an OLTP DBMS is bounded by the memory channel bandwidth, no matter how fast the CPU.

<center><figure><img src="tree-dram.png" alt="Traversing a B+ tree in DRAM."><br> <figcaption><i><b>Figure 1. Tree traversal in DRAM.</b> Traversing a B+ tree in DRAM requires fetching multiple nodes over a slow memory channel.</i></figcaption></figure></center>

Let's look into the simple example of traversing a B+ tree, which is a core component of OLTP DBMSs.
The tree nodes are stored in DRAM.
When the CPU traverses the tree, it first fetches the root node from DRAM and stores it in the cache.
Then, the CPU compares the keys, finds the next node, fetches it from DRAM, and stores it in the cache.
The process is repeated until we reach the leaf node.
Here, we can see that one tree traversal requires fetching multiple nodes from DRAM over the slow memory channel.
Although we can reuse the nodes in the CPU cache for future traversals, they are easily evicted and fetched again (especially the nodes at lower levels, which are rarely accessed) because the total size of frequently-accessed nodes exceeds the cache capacity.
This creates the memory channel bottleneck on OLTP DBMSs.

## Processing-in-Memory can overcome the memory channel bottleneck

_Processing-in-Memory (PIM)_ is a novel hardware device that replaces DRAM.
It is basically the same DRAM chip, except that a small general-purpose core (_PIM core_) is attached to it.
The PIM core has fast on-chip access to the DRAM (_PIM memory_), which can process the DRAM data in-place without needing to fetch it to the CPU through the slow memory channel.
Hence, PIM can fundamentally overcome the memory channel bottleneck.

<center><figure><img src="tree-pim.png" alt="Traversing a B+ tree in PIM."><br> <figcaption><i><b>Figure 2. Tree traversal in PIM.</b> PIM internally traverses B+ tree and minimizes required memory channel traffic.</i></figcaption></figure></center>

Recall the previous example of traversing a B+ tree, but this time stored in PIM.
The CPU first sends the target key to the PIM core.
Then, the PIM core fetches the root node from PIM memory, finds the next node, fetches it, and repeats.
When it reaches the leaf node, the result value is sent back to the CPU.
Compared to the previous example, the multiple nodes are fetched through the fast on-chip network, and we only need to transfer the key and value over the memory channel.
This greatly reduces the required memory channel traffic for the same traversal operation, and if applied for OLTP DBMSs, can potentially improve the transaction throughput as well. 

# Challenges for OLTP + PIM

PIM seems to be a promising hardware for overcoming the memory channel bottleneck and improving OLTP DBMSs.
However, our "OLTP + PIM" idea is not straightforward to implement in the real world because of the unique properties of the PIM hardware.
Let's go through three unique properties of the PIM device and corresponding challenges for designing a DBMS on top of it.

## PIM is divided into fine-grained modules

From a programmer's perspective, PIM is an accelerator device like a GPU - they both have processing cores and dedicated memory.
Each core in the GPU has access to the entire GPU memory ([_global memory_](https://docs.nvidia.com/cuda/cuda-c-programming-guide/index.html#memory-hierarchy) in CUDA terminology);
In other words, each GPU memory-resident data can be accessed from any GPU core.
This does NOT apply to PIM.
The PIM memory is divided into isolated _modules_, and each module has a _PIM core_ for processing data in the module.
Each PIM core has fast on-chip access to the local module's memory, but accessing other modules' memory incurs expensive off-chip communication.

<center><figure><img src="pim-partition.png" alt="PIM hardware organization.", style="width:60%"><br> <figcaption><i><b>Figure 3. PIM hardware organization.</b> PIM is divided into fine-grained modules. Each PIM core has fast access to its local memory, but accessing remote PIM memory is expensive.</i></figcaption></figure></center>

This constraint is due to the physical organization of PIM hardware, which is based on DRAM.
The above figure shows the organization of the PIM device and the corresponding DRAM components.
A DRAM DIMM consists of multiple chips, and each chip consists of multiple banks.
Similarly, a PIM DIMM consists of multiple PIM chips, and each chip consists of multiple PIM modules.
Here, you can see that different PIM modules are physically far from each other, making local accesses naturally faster than remote accesses.

When designing a DBMS, due to this constraint, the data structures should be partitioned across PIM modules in a fine-grained manner.
For example, a [PIM DIMM from UPMEM](https://github.com/upmem) consists of 128 PIM modules, each of which has 64MB capacity.
Thus, a typical server with 16 UPMEM DIMMs has 128GB PIM memory, but divided into 2048 modules.
**Partitioning a DBMS into thousands of fine-grained pieces is not an easy problem (Challenge 1).**

## Passive DRAM is better in some cases

PIM has the same hardware as DRAM, but additionally has small cores on each bank.
Hence, one might think that PIM is always better than passive DRAM.
However, this is not true because of the mismatch between the address interleaving scheme of DRAM and the partitioning of PIM modules.

<center><figure><img src="pim-interleaving.png" alt="PIM address interleaving.", style="width:70%"><br> <figcaption><i><b>Figure 4. Example address interleaving on PIM.</b> CPU views bytes horizontally, whereas each PIM module views bytes vertically.</i></figcaption></figure></center>

Traditionally, a CPU's virtual address space is interleaved across different DRAM banks to exploit parallelism.
For example, the first byte of a cache line is stored in the first chip's first bank, the second byte is stored in the second chip's first bank, and so on.
This is illustrated as horizontal boxes in Figure 4.
On the other hand, each PIM module corresponds to a DRAM bank, hence the bytes in the vertical boxes (which are physically placed together) go to the same module.
This makes it difficult to fetch data independently from a single PIM module, as contiguous bytes from a module are spread across different cache lines in the CPU's address space.
In sum, PIM stores data in a different layout from passive DRAM in order to process data in-place, so PIM is not suitable for merely storing individual data.
For this reason, PIM servers are equipped with both PIM and passive DRAM to exploit the advantage of both devices.

**When designing a DBMS, we should decide where to place each data in different types of memory (Challenge 2).**
If operations on the data get benefits from the PIM capability, they should be placed on the PIM side.
If not, it is better to place the data on DRAM, which provides a better interface with the CPU and a higher capacity.

## CPU to PIM execution switching takes time

A PIM system has two types of processors: a central CPU and thousands of PIM cores.
PIM cores have faster access to the data, but their processing power is weaker than that of the standard CPU due to the limitations of their silicon area.
Hence, we should exploit both CPU and PIM cores for the best performance.
The DBMS executes CPU codes for a while, offloads some operations to PIM cores, continues the CPU execution using the results, and so on.
However, the transition between the CPU and PIM core execution requires _PIM offload latency_.
For example, UPMEM PIMs have offload latency of 20 microseconds, which is much larger than typical DRAM access latency (hundreds of nanoseconds).

When designing a DBMS, this offload latency arises each time it processes the PIM-side data structure.
Since we want to offload as much data to PIM and exploit its near-data cores, the offload latency would easily become the performance bottleneck with naive approaches.
**Hence, we should decide how to hide this latency and maximize the transaction throughput (Challenge 3).**

# OLTPim Design

Motivated by the three aforementioned challenges related to PIM's hardware properties, solving them led to the development of [**OLTPim**: the first end-to-end OLTP DBMS for PIM](https://www.vldb.org/pvldb/vol18/p4241-kim.pdf).
OLTPim improves the existing in-memory transactional DBMS by storing some data in PIM memory and offloading relevant operations to the PIM cores.
It places and partitions data components in a principled manner to minimize expensive data movements, and utilizes lightweight batching to alleviate the overhead of offloading the operations.
Let's go over three interesting design choices of OLTPim.

## Near-memory affinity decides PIM vs. DRAM

<center><figure><img src="oltpim-nma.png" alt="Near-memory affinity examples."><br> <figcaption><i><b>Figure 5. Near-memory affinity of example operations.</b> Comparing the required memory channel traffic, B+ tree traversal should be offloaded to PIM but tuple fetching should not.</i></figcaption></figure></center>

First, OLTPim solves the **Challenge 2** (i.e., deciding to place each data in PIM or DRAM) using _near-memory affinity_, which measures how beneficial it is to offload the given operation to PIM.
Recall the example of traversing a B+ tree in Figures 1 and 2, again illustrated in the left side of Figure 5.
If the tree is stored in DRAM, we should fetch multiple tree nodes to the CPU, and the required memory channel traffic is \\(T_{DRAM} = Height \times NodeSize\\).
In contrast, if the tree is stored in PIM, we can offload the traversal to PIM cores and just send the key and get the value, so the required memory channel traffic is \\(T_{PIM} = (Key + Value)Size\\).
Here, the near-memory affinity \\(A_{near}\\) is defined as the following:
\\[A_{near} = T_{DRAM} - T_{PIM}\\]
Since \\(T_{DRAM}\\) is larger than \\(T_{PIM}\\) for the B+ tree traversal, its near-memory affinity is a large positive number, indicating that there is a large advantage if we offload it to PIM.

In the second example at the right side of Figure 5, imagine fetching a tuple.
Regardless of where the tuples are stored, simply fetching a tuple does not make a difference in the memory channel traffic.
Applying the same approach, the tuple fetching operation has zero near-memory affinity (\\(A_{near} = 0\\)), so there's no advantage of offloading it to PIM.

Recall that a transactional DBMS uses indexes, version chains, and tuples to serve OLTP workloads.
As discussed, traversing the indexes (i.e., the B+ trees) has high near-memory affinity, so OLTPim stores them in PIM.
Traversing the version chains (i.e., the linked lists) also has high near-memory affinity because we can offload the linked list traversal to PIM cores in a similar manner with the B+ trees.
Hence, OLTPim also stores them in PIM.
In contrast, fetching the tuples has zero near-memory affinity, so OLTPim stores the tuples in DRAM.

## Fine-grained partitioning based on primary key

<center><figure><img src="oltpim-partition.png" alt="OLTPim data partitioning.", style="width:50%"><br> <figcaption><i><b>Figure 7. Fine-grained partitioning in OLTPim.</b> The index entries and version chains are partitioned across the modules based on their primary keys.</i></figcaption></figure></center>

The second interesting design choice of OLTPim is that it maps the PIM-side data entries using their primary keys to solve the **Challenge 1** (i.e., fine-grained partitioning across thousands of PIM modules).
In OLTP workloads, _primary key_ is the unique identifier of a tuple in a table.
OLTPim evenly distributes index entries and version chains across the PIM modules based on the hash value of the primary key of their corresponding tuple, as depicted in Figure 7.
By doing so, version chains are placed in the same module with their relevant index entries, allowing PIM cores to traverse indexes and version chains at once.

When a user wants to locate a tuple, the CPU computes the module ID using the formula in Figure 7 and sends the input values to the corresponding module.
Then, the PIM core traverses the index using the primary key, traverses the version chain using the transaction ID, and finds the pointer to the visible version of the target tuple.
Since OLTPim stores tuples in DRAM, the output of the PIM operation is the DRAM pointer of the tuple.
Using this pointer, the CPU serves the transaction with the appropriate tuple.

Although the partitioned index is good at _point queries_ (finding one exact tuple with a given key), it cannot serve _range queries_ (finding all tuples between the key range) because the B+ tree's horizontal links are disconnected by PIM module boundaries.
OLTPim alleviates this limitation by assigning adjacent primary keys to the same module, allowing horizontal traversals to some degree.
When computing the module ID, Figure 7 shows that OLTPim optionally shifts the key to the right by \\(R\\) bits to place \\(2^R\\) adjacent keys to the same module.
The user can configure the R value of an index based on the maximum scan length of range queries in the workload, and OLTPim can serve each of them by accessing no more than two PIM modules.

## Lightweight batching without OS intervention

<center><figure><img src="oltpim-batch.png" alt="Batching on OLTPim.", style="width:60%"><br> <figcaption><i><b>Figure 8. Batching in OLTPim.</b> The batcher component accumulates the requests and sends them to the corresponding PIM modules in a batch.</i></figcaption></figure></center>

Lastly, the final interesting design choice of OLTPim is that it solves the **Challenge 3** (i.e., hiding PIM offload latency) by processing multiple requests _in a batch_.
Instead of offloading one operation to PIM and waiting until it's done, OLTPim first accumulates requests to a request list (shown in the batcher in Figure 8), batch-copies them to the corresponding PIM modules, and batch-processes the operations.
This method amortizes the PIM offload latency across a large batch of requests and improves the total transaction throughput.

Although batching improves the performance, it requires a more complicated system design, which results in additional overhead.
Concurrently executing a large batch of transactions requires multiple threads, and switching between them frequently incurs significant OS overhead.
The need for the CPU to control the PIM devices further aggravates the problem because the control code should be run concurrently, which requires a separate thread in a naive approach.
OLTPim solves the problem by replacing the threads with [_coroutines_](https://en.cppreference.com/w/cpp/language/coroutines.html), which are lightweight user-level implementations of threads that don't require OS intervention.
Furthermore, the PIM control codes are executed with [_flat combining_](https://www.cs.tau.ac.il/research/moran.tzafrir/papers/spaa2010_flat_combining.pdf) algorithm.
Instead of the threads/coroutines to offload the PIM control to another thread, they acquire a global lock and run the control logic themselves whenever needed.
As a result, OLTPim's batcher completely avoids OS overheads and maximizes the transaction throughput.


# Evaluation

Using the design choices discussed above, OLTPim is implemented and evaluated on a dual-socket server with 2 Xeon Silver 4216 CPUs and 12 memory channels, where 8 of them are equipped with real PIM devices from [UPMEM](https://github.com/upmem) and the other 4 channels are equipped with passive DRAMs.
The OLTPim performance is compared with a baseline system [MosaicDB](https://www.vldb.org/pvldb/vol17/p577-huang.pdf), a state-of-the-art research OLTP DBMS.
It is evaluated on the same server, except that all 12 memory channels are equipped with passive DRAMs to maximize the total memory bandwidth for the baseline.
The workloads are [YCSB](https://pages.cs.wisc.edu/~akella/CS838/F15/838-CloudPapers/ycsb.pdf) and [TPC-C](https://www.tpc.org/tpcc/) with different read-write ratios. Each version of YCSB is named as C (100% read), B (95% read, 5% write), and A (50% read, 50% write).
The metrics are _transaction throughput_ (million transactions per second) and _memory channel traffic per transaction_ (kilobytes per transaction).

<center><figure><img src="result.png" alt="Evaluation result."><br> <figcaption><i><b>Figure 9. Evaluation result.</b> Transaction throughput and memory channel traffic per transaction on YCSB and TPC-C workloads. Black points are from MosaicDB, and red points are from OLTPim.</i></figcaption></figure></center>

As shown in Figure 9, OLTPim achieves higher throughput with less memory traffic in most cases.
On YCSB workloads, the improvements become higher as the table size grows, and OLTPim shows up to 1.71x throughput with only 6.14x less memory traffic.
On TPC-C workloads, OLTPim also uses less memory channel traffic than the baseline and achieves higher throughput on the read-only workload mix.

Note that OLTPim's advantage is more apparent on larger table sizes.
The throughput and memory traffic of MosaicDB become worse on large tables because the CPU cache cannot hide their large working set.
In contrast, OLTPim's performance remains the same on large tables, making it more scalable.
This is because PIM avoids the memory channel bottleneck by processing the DRAM data in-place.


# Conclusion

Transactional database systems suffer from a performance bottleneck due to the slow memory channel between the CPU and DRAM.
PIM can overcome this bottleneck by processing the DRAM-resident data in place using a small core attached to the DRAM chip.
However, naively moving the DBMS to PIM does not work because (1) PIM is divided into thousands of isolated modules, (2) some operations are inefficient when offloaded to PIM, and (3) offloading an operation to PIM incurs large latency.
To address the challenges, OLTPim stores indexes and version chains in PIM and tuples in DRAM based on the near-memory affinity of the relevant operations.
For the PIM-side data, it evenly distributes them across thousands of modules based on their primary key.
The transaction requests are batch-processed to hide the PIM offload latency while minimizing the OS overheads.
OLTPim is implemented and evaluated on a real PIM system from UPMEM, and it shows higher throughput with less memory channel traffic compared to the state-of-the-art research OLTP DBMS.

_This post is based on the research paper [No Cap, This Memory Slaps: Breaking Through the Memory Wall of Transactional Database Systems with Processing-in-Memory](https://www.vldb.org/pvldb/vol18/p4241-kim.pdf), published in [VLDB 2025](https://www.vldb.org/2025/)._
