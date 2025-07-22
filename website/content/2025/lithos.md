+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "LithOS: An Operating System for Efficient Machine Learning on GPUs"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2025-07-15

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Artificial Intelligence", "Systems"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
# Consider these similar to keywords specified for a research paper.
tags = ["GPU", "operating system"]

[extra]
author = {name = "Patrick H. Coppock", url = "http://cherry.lan.cmu.edu/~packy/" }
# The committee specification is a list of objects similar to the author.
committee = [
    {name = "Zhihao Jia", url = "https://www.cs.cmu.edu/~zhihaoj2/"},
    {name = "Phil Gibbons", url = "https://www.cs.cmu.edu/~gibbons/"},
    {name = "Nathan Beckmann", url = "https://www.cs.cmu.edu/~beckmann/"}
]
+++

# Introduction

GPUs are expensive.

Applications get full GPUs but may not use them efficiently. For example,
inference servers don't execute large batches continuously. There are both
temporal and spatial aspects to this inefficiency.

What do we do when a resource becomes scarce? We share it. We did this for CPUs
with timesharing. When multiple cores came around, we extended our operating
systems to allocate these resources both spatially and temporally (_n_ cores
for _t_ time).

More recently, we've developed GPU sharing systems. Some share the GPU
temporally, others, spatially.

In the rest of this post, I'll be focusing on NVIDIA technology and using their
terminology.

GPUs were first shared via a time-slicing mechanism where applications'
contexts are switched every quarter of a millisecond or so. If an application
becomes idle, the next is allowed immediately to run. Time slicing remains the
default method of sharing the GPU today.

Limitations of time slicing (besides not supporting spatial sharing) include
that all contexts are treated similarly. Each application gets a proportional
share of the GPU. While this can be fair, it fails to account for the diverse
application requirements of today's GPU applications. A class of work addresses
this drawback by supporting application priority, e.g., TGS and REEF.

Spatial stacking is necessary. As GPUs scale in size, existing applications
require a smaller share. While they may execute faster on a larger compute
engine, it is less efficient. To support this spatial stacking, multi-instance
GPU (MIG) was developed. Users are able to partition the GPU into one or more
"instances," and allocate these to applications. Unfortunately, MIG instances
are expensive to configure (~1s), and MIG is unable to support the kind of
fine-grained sharing that interactive GPU applications could utilize.

With multi-process service (MPS), NVIDIA breaks down all forms of partitioning
and maximizes device utilization by combining all applications into a single
hardware context. Scheduling between different applications is done with
neither fairness or more specific application requirements in mind.

Orion and MPS client priority improve on this by buffering application work and
prioritizing launches of some applications over others.

What is needed is a GPU sharing system / scheduler / operating system that both
allows for the high utilization of MPS with the fine-grained temporal
partitioning of time slicing and spatial partitioning even more fine-grained
than MIG's GPCs.

# Design

![LithOS integrates multiple mechanisms to effectively manage GPUs](design.pdf)

To this end, my team has developed LithOS.

The LithOS architecture is similar to some prior works, interposing the CUDA
API, buffering GPU tasks, and performing scheduling normally left up to the
device. However, LithOS integrates a few components to successfully provide
the high utilization of MPS with the effective isolation of time slicing and
MIG.

## Arrogating GPU Scheduling with Virtual Streams

GPUs are typically programmed by launching memory copies and many kernels,
filling up GPU pipelines and then waiting for these tasks to complete. While
very effective for single applications attempting to use the GPU's extensive
capacity, this programming model isn't conducive to scenarios where multiple
applications share GPU resources. GPU hardware schedulers are
throughput-oriented, ignoring fairness concerns.

LithOS must reclaim from the GPU the onus of scheduling tasks, without
uncovering the latencies associated with GPU computation. LithOS does this by
means of software command queues. Specifically, LithOS intercepts application
task submission and enqueues the tasks in its own queues. A LithOS daemon
thread dequeues operations and submits them to the GPU, respecting control flow
dependencies and limiting the number of outstanding tasks.

By limiting the number of outstanding tasks, LithOS reserves the option of
throttling one application to allow another to make faster progress. In this
way, LithOS can ensure application SLOs are met.

## Cheaply Estimating Task Durations

To schedule GPU work, LithOS limits the amount outstanding. Too little, and GPU
communication overheads take over, greatly reducing application performance.
Too much, and LithOS is unable to reclaim resources in response to shift
application loads. A challenge is that it is unknown how long a task may take.
While tasks like memory copies or memory sets have somewhat deterministic
latencies, it is impossible to predict how long arbitrary kernel code will
take.

However, GPU workloads are often regular. Neural network training is a loop
where similar GPU tasks are launched in each iteration. Inference service
launches the same model graphs repeatedly in response to queries. LithOS'
latency model uses this regularity to predict how long a previously executed
task will take. The model retains a recent window of past task durations.

## Slicing Grids for Fine-grained Scheduling in Time

![Slicing enables optimal scheduling.](timeline.pdf)

In order to schedule application tasks, LithOS must be able to bound the time
a task takes. If a task were allowed to run for indefinite time, LithOS would
be unable to reclaim its resources for other tasks. In CPU land, this is done
via timer interrupts and context switching. NVIDIA's time slicing does this;
however, third-party software doesn't have access to the SM interrupt handlers
that enable such context switching.

LithOS takes a different approach: kernel slicing. Kernels are launched as
grids of many thread blocks. Generally, the GPU programming model allows for
the thread blocks to execute in any order, simultaneously or not. LithOS
interposes application kernel launches, and breaks them up into multiple
launches, each with a subset of the thread blocks in the original launch.

Kernel launches are not free, and LithOS slicing, while entirely transparent to
GPU programmers, has additional overhead. How does LithOS manage the trade-off
between slice size and agile scheduling?

The applications which LithOS targets---inference service and neural network
training---typically have SLOs no more strict than a tens of milliseconds. To
fill these needs, LithOS must be able to reschedule resources within a similar
timeframe. Using the task latency model, LithOS slices grids into 500μs pieces.
Many kernels already complete within this timeframe and do not require slicing.
This quantum amortizes the launch overhead, which is under 10μs.

## Masking TPCs for Fine-grained Scheduling in Space

A major feature of LithOS is the ability to stack applications _spatially_,
allowing them to execute simultaneously on disjoint sets of SMs. While MIG
allocates GPCs, it is possible to allocate on the smaller granularity of TPCs.
LithOS does this, masking off TPCs for each kernel launch. This enables
efficient, isolated use of GPU compute.

TPC masking interacts with the task latency model. Depending on higher-level
LithOS policy, tasks may execute at different times with different TPC masks.
The task latency model fits a linear regression for transformed Amdahl's Law
to predict task duration as a function of TPCs assigned.

# Results

We implemented LithOS in about 5000 lines of code and evaluated it along two
metrics for a set of neural network models.
We compare LithOS to time slicing, MPS, and MIG, as well as three other
state-of-the-art systems, REEF, TGS, and Orion.

We stack three applications together, a high-priority service (HP A), a
closed-loop high-priority job (HP B), and a best-effort job (BE).

GPU sharing should both maximize GPU utilization and fulfill application SLOs.
System throughput is a good proxy metric for GPU utilization. Application SLOs
are 

## 

# Conclusion
