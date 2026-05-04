+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "LithOS: An Operating System for Efficient Machine Learning on GPUs"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2025-12-09

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
    {name = "Sam Arch", url = "https://samarch.xyz"},
    {name = "Phil Gibbons", url = "https://www.cs.cmu.edu/~gibbons/"}
]
+++

# Introduction

Not only are GPUs expensive, they are also too often idle. Bursty machine
learning (ML) inference requests leave gaps in time. Even when jobs are busy,
they may be compute- or memory-bound, leaving the other resource underutilized
(in space). The obvious solution to underutilization is to share the device
among muliple applications, or, tenants. To mop up cycles left over from a
bursty ML inference server, a continuous training loop can be colocated. Not to
waste compute when a memory-bound long-context large lanugage model (LLM)
instance is executing, another, more--compute-bound ML inference instance can
be colocated.

GPUs can be shared either temporally or spatially. Temporal sharing (i.e., time
sharing) allows device utilization to be improved over the case where a single
bursty job executes. Spatial sharing helps in cases where two applications are
bound on different resources (e.g., compute and memory bandwidth).

A major tension drives this space. While expensive GPUs must be highly
utilized, each application's service-level objectives (SLO) must be met.
Today's GPU systems offer either device-centric high utilization and system
throughput or application-centric performance isolation and predictably low
latency. LithOS is the first system effectively to mediate between these two
concerns.

![LithOS design: virtual streams, online runtime prediction, kernel slicing,
and per-launch TPC masking.](design.png)

_Figure: LithOS interposes the CUDA Driver API, predicts runtimes online,
slices kernels, and allocates processing resources to each kernel launch to
realize policy on hardware._

This post focuses on NVIDIA hardware and terminology. The default sharing
mechanism is time slicing (TS). With this mechanism, the device switches
application contexts every few hundred microseconds, and if one app idles, the
next runs immediately. Time slicing is simple and fair---each context gets a
proportional share---but it neither supports spatial sharing nor accounts for
diverse requirements. Prior work ([TGS](
https://www.usenix.org/conference/osdi22/presentation/han)) enforces priority
to temper "fairness" with service goals but cannot overcome the limits of
coarse temporal multiplexing alone.

As GPUs increase in size, spatial sharing helps improve utilization. With
[Multi-Instance GPU (MIG)](
https://docs.nvidia.com/datacenter/tesla/mig-user-guide/), users carve a device
into a several instances and hand those to apps. MIG provides isolation, but
the units are coarse and reconfiguration takes about a second which is too slow
for interactive or shifting workloads.

At the other end, NVIDIA’s [Multi-Process Service (MPS)](
https://docs.nvidia.com/deploy/mps/index.html) maximizes utilization by
collapsing tenants into a single hardware context. This keeps the device busy
but cannot provide fairness or allow administrators to otherwise tune resources
shares. The app that launches more work tends to hog the GPU. Systems like
[REEF](https://www.usenix.org/conference/nsdi23/presentation/wu), [Orion](
https://doi.org/10.1145/3627703.3629578), MPS client priority mitigate this
by buffering and prioritizing launches, yet they inherit MPS's lack of
fine-grained time/space control.

What's missing is a GPU _operating system_ that unifies software control over
time and space so the device stays busy without sacrificing predictable
performance.

The core barriers are: (1) you can’t preempt arbitrary GPU kernels at fine
granularity, and (2) MIG’s coarse spatial units make dynamic partitioning
impractical. LithOS addresses both in software.

LithOS is our attempt to reconcile these goals with a principled, OS-like
approach to GPUs. The key idea is to pull scheduling decisions back into
software, where we can apply policy, while still feeding the device enough work
to keep it busy. LithOS interposes application submissions, understands
dependencies, estimates task durations online, and enforces fine-grained
in both time and space---without requiring application changes.

At a glance, LithOS contributes:

- Virtual streams: reclaim launch control from the device scheduler while
  preserving application concurrency.
- Online latency micro-models: predict per-task runtime and scale predictions
  with assigned compute share.
- Transparent kernel slicing: bound preemption latency to hundreds of
  microseconds with negligible overhead on common kernels.
- Per-launch resource allocation: enable fine-grained spatial sharing for
  simultaneous, isolated execution.
- SLO-friendly scheduling: priority, fairness, and tail-aware admission at
  slice granularity.

The rest of this post dives into how these pieces fit together and what they
buy you in practice.

# Design

LithOS interposes the CUDA API, buffers GPU tasks, and performs scheduling
normally left to the device. The key difference is integrating four
pieces---virtual streams, a tiny latency model, slicing, and thread processing
cluster (TPC) masking---to achieve both MPS-like utilization and MIG-like
isolation.

## Reclaiming GPU Scheduling with Virtual Streams

CUDA apps flood the device with copies and kernels, which is great for a single
tenant but problematic when many tenants share a GPU: the hardware scheduler
prioritizes throughput over QoS. LithOS intercepts submissions into software
queues (**virtual streams**), maintains a bounded amount of outstanding work,
and issues operations while respecting stream dependencies between kernels.

Keeping a small cushion of ready work per physical stream keeps the GPU busy;
bounding the cushion lets LithOS throttle or admit slices to meet SLOs. LithOS
preserves intra-app concurrency by tracking events and stream order. Policy
hooks live on these queues: high-priority (HP) services get dedicated TPCs;
best-effort (BE) work drains opportunistically.

## Cheaply Estimating Task Durations

To keep the device busy yet preempt quickly, LithOS must know "how long will
this take if I give it \\(k\\) TPCs now?" ML workloads are repetitive (training
loops, repeated inference graphs), so we learn from recent launches.

LithOS maintains per-(kernel, shape) micro-models keyed by salient launch
parameters and aggregates recent durations (with the outlier-insensitive
median). To predict across spatial shares, we use a simple transformed-[Amdahl
](https://en.wikipedia.org/wiki/Amdahl's_law) model:

$$
T(k) = T_\text{parallel} \cdot \frac{1}{k} + T_\text{serial}
$$

Here, \\(k\\) is the assigned TPC count. We express this as a relationship
linear in \\(\frac{1}{k}\\). As each submitted kernel completes, its
corresponding \\(T_\text{serial}\\) and \\(T_\text{parallel}\\) are updated.
These models enable us to limit the amount of outstanding work while still
keeping the device busy. No offline profiling is needed; we weight recent data
and fall back to conservative caps for new kernels.

## Slicing Grids for Fine-grained Scheduling in Time

![Slicing enables optimal scheduling by bounding preemption latency with short
kernel slices.](slicing.png)

_Figure: LithOS slices kernels into ~500μs chunks to bound preemption latency
while keeping the GPU busy._

To bound preemption latency, LithOS slices kernels. Kernels launch as grids of
blocks; we transparently split a grid into multiple launches, each covering a
subset of blocks. We use a 500μs quantum which is large enough to amortize
<10μs launch overhead but small enough to preempt HP work quickly. Many kernels
already fit and need no slicing.

There are a few edge cases that we can't support. First, persistent/cooperative
kernels that need all blocks resident shouldn't be sliced. Second, tiny kernels
under the quantum are left intact. Because slicing happens at submission time,
apps require no code changes.

## Masking TPCs for Fine-grained Scheduling in Space

LithOS stacks applications spatially, enabling simultaneous execution on
disjoint streaming multiprocessor (SM) sets. Hardware limitations require that
LithOS schedule pairs of SMs, or, TPCs. LithOS stealing policy reshapes
applications on the fly: e.g., give 1/3 of TPCs to HP work for 1ms while a
training job executes on the rest; when the HP queue drains, the BE job
expands---no MIG reconfig needed.

# Results

We implemented LithOS in about 5000 lines of code and evaluated it along two
metrics for a set of neural network models. We compare LithOS to both
existing NVIDIA sharing systems (time slicing, MPS, and MIG) and
state-of-the-art research systems (REEF, TGS, and Orion). To compare with MPS,
we add two configurations to the basic MPS setup, client _priority_ and active
thread percentage _limits_.

We stack three applications together, a high-priority service (HP A), a
closed-loop high-priority job (HP B), and a best-effort job (BE). For systems
which support partitioning (MIG, limits, and LithOS), we allocate 75% to HP A
and 25% to HP B. MIG partitioning is inflexible, so we make due with a 4/7 and
3/7 partitions. For systems which support priority, (priority, REEF, TGS,
Orion, and LithOS), we reduce the priority of the BE application. On LithOS,
this just means zeroing its TPC quota, so that it can only steal.

GPU sharing should both maximize GPU utilization and fulfill application SLOs.
System throughput is a good proxy metric for GPU utilization. Application SLOs
are measured via the tail of latency distributions (e.g., 99th percentile) for
LC services and throughput for the HP/BE jobs. We report both ends of this
trade-off and show that LithOS improves the Pareto frontier relative to prior
mechanisms.

Our evaluation uses representative neural-network workloads (compute- and
memory-bound). We compare on modern NVIDIA datacenter GPUs.

## Pushing the Pareto Frontier

![LithOS provides the utilization of MPS with the isolation of MIG.](
trade-off.png)

_Figure: LithOS keeps throughput near MPS while tracking SLO attainment close
to isolated baselines by dynamically reshaping time/space allocations._

The figure plots system throughput against SLO attainment. Ideally, you want
to be toward the top right. MPS is near the bottom right: high throughput but
unbounded interference limits SLO attainment. MIG and TS move up but at the
cost of throughput: static partitions and frequent idle time waste compute when
load shifts. Other research systems, as well as MPS client _priority_ and
active thread _limits_, moderate the trade-off with less-than-ideal throughput
and SLO attainment.

LithOS bends the curve. By keeping the device busy and giving the HP
applications priority on their TPC quotas, LithOS stays close to MPS throughput
while matching SLO attainment to its isolated baseline (MIG). As load ebbs and
flows, the scheduler continuously reshapes time/space allocations, avoiding the
reconfiguration penalties that make MIG sluggish.

## Allocating Performance

![LithOS services high-priority applications while allowing some best-effort
execution.](goodput.png)

_Figure: Unlike all other systems, LithOS both perfectly services high-priority
applications and allows significant best-effort execution._

How does LithOS push the latency/throughput Pareto frontier? Comparing all
evaluated systems in terms of goodput (throughput under SLO), broken down
according to each of the three colocated applications. Similar to partitioning
systems like MIG and TS, it isolates HP A from the noisy neighbors that plague
MPS-like sharing. But unlike static partitions, it doesn't waste capacity. In
mixed HP/BE experiments, LithOS maintains HP SLOs and assigns the remaining
TPCs to BE jobs. When HP traffic spikes, the BE yields quickly; when traffic
subsides, the BE ramps back up. Best-effort work runs when it won't jeopardize
SLOs.

## Successfully Limiting Tail Latencies

![LithOS successfully limits tail latencies by preventing interference.](
latency.png)

_Figure: With LithOS, tail latencies shrink due to spatial partitioning and
bounded preemption latency._

Without partitioning, sharing systems are unable to limit tail latencies. These
diverge on MPS, priority, REEF, and Orion. Temporal partitioning systems limit
this to some extent. LithOS keeps latencies close to isolated execution and is
the only system that meets all SLOs. Specifically, LithOS reduces tail
latencies 13× vs. MPS and 12× vs. Orion.

# Limitations and what we don't (yet) do

LithOS has a few limitations:

- Cooperative/persistent kernels prevent slicing.
- It does not manage memory by allowing for swapping to the CPU.
- Because it depends on MPS for multi-context support, LithOS cannot isolate
  hardware faults.

Despite these, the common path---ML training loops and inference
graphs---benefits without code changes.

# Conclusion

LithOS treats the GPU as a shared compute fabric that deserves an operating
system. By interposing at the CUDA boundary, learning task times, slicing to
bound preemption, and masking TPCs to stack tenants, LithOS delivers MPS-like
utilization with MIG-like isolation.

For practitioners:
- Run latency-critical inference next to background jobs and claw back
  utilization while keeping tails in check.
- Consolidate many small/bursty jobs by sharing at TPC granularity; LithOS
  reshapes shares as load shifts.
- Skip per-model profiling—LithOS learns online and adapts.

We believe this is the right abstraction boundary for the next generation of ML
infrastructure: a GPU OS that balances policy with performance, without
changing CUDA code.
