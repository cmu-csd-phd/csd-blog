+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "LithOS: An Operating System for Efficient Machine Learning on GPUs"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2025-10-23

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

GPUs are expensive---and too often underutilized. Many applications are given
an entire device even though their demand is bursty or small. Inference
servers, for example, don't run large batches continuously; training loops
alternate between compute-heavy and copy-heavy phases. Inefficiency shows up in
two dimensions: in time (idle gaps between bursts) and in space (idle cores
when the job can't saturate a large GPU).

When resources become scarce, we share them. The CPU world learned this decades
ago with timesharing, later evolving to allocate both time and cores. The same
trajectory is now playing out for GPUs: a growing ecosystem of mechanisms
attempts to share accelerators either temporally, spatially, or both.

This post focuses on NVIDIA hardware and terminology. The default sharing
mechanism is
time slicing: the device switches application contexts roughly every few
hundred microseconds, and if one app idles, the next runs immediately. Time
slicing is simple and fair---each context gets a proportional share---but
it neither supports spatial stacking nor accounts for diverse requirements.
Prior work (e.g., TGS, REEF) adds priority to temper "fairness" with service
goals, but cannot overcome the limits of coarse temporal multiplexing alone.

Spatial partitioning helps in a world of ever-larger GPUs. With Multi-Instance
GPU (MIG), users can carve the device into a few instances and hand those to
different apps. MIG provides isolation, but its granularity is coarse and
reconfiguration takes on the order of a second---too slow for interactive or
rapidly shifting workloads.

On the other end, NVIDIA’s Multi-Process Service (MPS) maximizes utilization by
collapsing tenants into a single hardware context. This keeps the device busy
but offers little policy: without additional control, the application that
launches more work tends to win. Systems like Orion and MPS client priority
mitigate this by buffering and prioritizing launches, yet they still inherit
MPS's lack of fine-grained time/space control.

What's missing is a GPU "operating system" that combines the utilization of
MPS, the agility of time slicing, and the isolation of spatial
partitioning---ideally at a finer granularity than MIG's GPCs and with
sub-millisecond responsiveness.

Put differently, modern ML serving and training clusters grapple with a
three-way tension:

- Utilization: keep expensive accelerators busy even when individual jobs are
  bursty or small.
- Isolation: protect critical services from noisy neighbors and bound tail
  latency.
- Agility: reallocate capacity quickly as load shifts, without heavy
  reconfiguration or restarts.

Existing mechanisms hit only two corners at best. Time slicing gives isolation
and agility but bleeds utilization with
no spatial stacking. MIG offers hard isolation, but its coarse granularity and
second-scale reconfiguration make it ill-suited to dynamic workloads. MPS
wrings out utilization, but without policy it devolves into "whoever launches
more wins," which is unacceptable for SLO-driven services.

LithOS is our attempt to reconcile these goals with a principled, OS-like
approach to GPUs. The key idea is to pull scheduling decisions back into
software, where we can apply policy, while still feeding the device enough work
to keep it saturated. LithOS interposes application submissions, understands
dependencies, estimates task durations online, and enforces fine-grained time
and space partitioning at sub-millisecond and sub-GPC granularity---without
requiring application changes.

At a glance, LithOS contributes:

- A virtual-streams abstraction that reclaims launch control from the device
  scheduler while preserving application concurrency.
- An online latency model that predicts per-task runtime and scales predictions
  with assigned compute share.
- Transparent kernel slicing that bounds preemption latency to hundreds of
  microseconds with negligible overhead on common kernels.
- Per-launch TPC masking that enables spatial stacking at finer granularity
  than MIG, enabling simultaneous, isolated execution.
- SLO-friendly scheduling policies that combine priority, fairness, and
  tail-latency control while maintaining high device occupancy.

The rest of this post dives into how these pieces fit together and what they
buy you in practice.

# Design

![LithOS integrates multiple mechanisms to effectively manage GPUs](design.pdf)

To this end, my team has developed LithOS.

The LithOS architecture is similar to some prior works, interposing the CUDA
API, buffering GPU tasks, and performing scheduling normally left up to the
device. However, LithOS integrates a few components to successfully provide
the high utilization of MPS with the effective isolation of time slicing and
MIG.

## Architecture at a glance

LithOS comprises a lightweight user-space library that applications preload and
a daemon that arbitrates the GPU.

- The interposer library wraps CUDA APIs (streams, events, _memcpy_()s, kernel
  launches). Applications keep using their existing code; LithOS captures the
  intent.
- A per-application shim translates these calls into a neutral IR: a DAG of
  operations (copies, sets, kernels) with dependencies and resource hints.
- A central daemon maintains a queue per application (a "virtual stream" set),
  learns task durations, and schedules slices onto the physical GPU streams
  according to cluster policy.
- An enforcement layer applies per-launch constraints (slice sizes, TPC masks,
  outstanding work caps) and meters memory-bandwidth--sensitive operations.

This separation mirrors classic OS design: apps interact with a narrow API; the
kernel decides when and where work runs; enforcement ensures decisions manifest
on the hardware.

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

Two practical questions arise when reclaiming control from the hardware
scheduler:

1) How do we keep the GPU fed? LithOS never drains the device; it maintains a
   small cushion of ready work per physical stream (e.g., a few slices and
   _memcpy_()s ahead) so kernels can back-to-back issue. This cushion is tuned
   dynamically from the latency model to balance utilization and preemption
   latency.
2) How do we honor application concurrency? Developers often rely on CUDA
   streams to expose graph parallelism. LithOS preserves intra-app ordering and
   overlap by tracking dependencies (events, stream order, implicit barriers)
   and mapping the app's many virtual streams onto a controlled number of
   physical streams, similar to multiplexing OS threads onto cores.

Virtual streams also give us a place to attach policy. For example, a
high-priority service can receive a larger outstanding-work budget and
immediate admission for latency-critical slices, while best-effort jobs drain
opportunistically.

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

Concretely, LithOS maintains per-(kernel, shape) micro-models keyed by salient
launch parameters (grid, block, problem size). We use medians for a robust
aggregate to smooth short-term jitter. To extrapolate across spatial
allocations, we embed a simple transformed-Amdahl model:

$$
t(p) \approx t_\text{serial} + t_\text{parallel} / f(p)
$$

where \\(p\\) is the assigned TPC share and \\(f(p)\\) captures diminishing
returns at low occupancy. A tiny online regression updates
\\(t_\text{serial}\\) and \\(t_\text{parallel}\\) from observed slices. The
scheduler then asks: "If I give this app \\(k\\) TPCs for the next 2ms, how
much of its queue clears?" Those forecasts drive both admission and the size of
the outstanding-work cushion.

This model is deliberately humble. It avoids offline profiling, respects drift
(weights recent data), and falls back to conservative caps for
never-before-seen kernels until measurements arrive. In practice, the
regularity of ML loops means the model converges within a handful of
iterations.

## Slicing Grids for Fine-grained Scheduling in Time

![Slicing enables optimal scheduling.](slicing.pdf)

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

There are important edge cases:

- Persistent/cooperative kernels that rely on all blocks resident at once are
  can result in hangs when sliced. For applications consisting of such kernels,
  slicing should be disabled.
- Tiny kernels that already complete within the quantum are left intact to
  avoid death-by-a-thousand-launches.

Because slicing happens at submission time, apps require no code changes.
LithOS rewrites a launch of B blocks into a sequence of launches with B1, B2,
... blocks whose union is the original set, interleaving slices from other
applications according to policy.

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

Putting time and space together, LithOS can, for example, dedicate one third of
the TPCs to a latency-critical service for the next millisecond, while letting
a training job stream through slices on the remaining TPCs. A millisecond
later, if the service's queue drains, its share shrinks automatically and the
best-effort job expands to fill the slack---no MIG reconfiguration required.

## Compatibility, safety, and deployment

LithOS is designed to be a drop-in for most CUDA apps. A few caveats are worth
noting:

- Cooperative kernels and device-side launches are supported but may restrict
  slicing opportunities.
- Memory oversubscription is out of scope; LithOS does not swap device memory.
  It can, however, meter allocation-heavy phases to reduce stalls.
- Security/tenancy isolation is best-effort at the performance level; for hard
  isolation guarantees, MIG remains complementary. LithOS can run within a MIG
  instance to add agility inside a static partition.

# Results

We implemented LithOS in about 5000 lines of code and evaluated it along two
metrics for a set of neural network models.
We compare LithOS to time slicing, MPS, and MIG, as well as three other
state-of-the-art systems, REEF, TGS, and Orion.

We stack three applications together, a high-priority service (HP A), a
closed-loop high-priority job (HP B), and a best-effort job (BE).

GPU sharing should both maximize GPU utilization and fulfill application SLOs.
System throughput is a good proxy metric for GPU utilization. Application SLOs
are measured via the tail of latency distributions (e.g., 99th percentile) for
LC services and completion time/throughput for HP/BE jobs. We report both ends
of this trade-off and show that LithOS improves the Pareto frontier relative to
prior mechanisms.

Our evaluation uses a suite of representative neural-network workloads spanning
compute-bound and memory-bound kernels, with both steady-state training loops
and bursty inference traffic. We evaluate on modern NVIDIA datacenter GPUs with
recent drivers and contrast LithOS against: (1) time slicing (TS), (2) MPS, (3)
MIG configured to share the device across tenants, and (4) three research
systems---REEF, TGS, and Orion---configured per their recommended settings. All
systems run the same binaries.

## Pushing the Pareto Frontier

![LithOS provides the utilization of MPS with the isolation of MIG.](
    trade-off.pdf)

The figure plots system throughput against SLO attainment. Ideally, you want
to be toward the top right. MPS is near the top left: high throughput but
unbounded interference limits SLO attainment. MIG and TS move you right but at
the cost of capacity: static partitions and frequent idle time waste compute
when load shifts. Other research systems moderate the trade-off with
less-than-ideal throughput and SLO attainment.

LithOS bends the curve. By keeping slices queued just-in-time and giving LC
slices first refusal on a small fraction of TPCs when they near deadlines,
LithOS stays close to MPS throughput while tracking SLO attainment to its
isolated baseline. As load ebbs and flows, the scheduler continuously reshapes
time/space allocations, avoiding the reconfiguration penalties that make MIG
sluggish.

## Correctly Allocating Performance

![LithOS services critical applications while allowing best-effort execution.](
    goodput.pdf)

How does LithOS push the latency/throughput Pareto frontier? Similar to the
partitioning systems MIG and limits, it successfully isolates HP A from the
noisy neighbors that plague MPS-like sharing. But unlike static partitions, it
doesn’t strand capacity. In mixed LC/HP/BE experiments, LithOS maintains LC
SLOs and assigns the remaining TPCs to HP and BE jobs. When LC traffic spikes,
BE yields quickly (sub-millisecond) and HP absorbs a controlled slowdown; when
traffic subsides, BE ramps back up without handoffs or instance churn.

We call this "goodput-aware" allocation: best-effort work only runs when it
won't jeopardize SLOs.

## Successfully Limiting Tail Latencies

![LithOS successfully limits tail latencies by preventing interference.](
    latency.pdf)

Without partitioning, sharing systems are unable to limit tail latencies. These
diverge on MPS, priority, REEF, and Orion. Temporal partitioning systems are
able to limit this to some extent and perform better. LithOS effectively limits
latencies close to the isolated execution of MPS limits and is the only system
that meets all SLOs. Specifically, LithOS reduces tail latencies 13× compared
to MPS and 12× compared to Orion.

Why do tails shrink? Two reasons:

- Bounded preemption latency from slicing: LC work is never stuck behind a
  multi-millisecond kernel.
- Spatial masking during LC bursts: LC kernels run on a clean subset of TPCs,
  reducing queueing and cache pollution from neighbors.

These mechanisms act conservatively. If a kernel cannot be sliced safely, or a
mask would cause correctness issues, LithOS falls back to temporal sharing
while maintaining admission control.

## Methodological notes

We evaluate steady-state behavior (minutes) rather than transient
micro-benchmarks. All curves are averaged over multiple runs with confidence
bands; we pin CUDA driver and runtime versions across systems for fairness.
Results focus on relative deltas---exact numbers vary across GPUs and driver
releases---but the qualitative trends are robust: combining just-in-time
scheduling with sub-millisecond slicing and fine-grained spatial partitioning
consistently improves the latency–throughput trade-off.

# Limitations and what we don’t (yet) do

Like any OS, LithOS makes trade-offs:

- Cooperative/persistent kernels constrain slicing.
- Collectives and multi-GPU jobs introduce global barriers outside a single
  device's purview. LithOS preserves local ordering but cannot eliminate
  cross-device tail amplification.
- Device memory is not oversubscribed or paged; if you need more than fits, you
  still need model parallelism or activation checkpointing at the framework
  level.
- Hard security isolation (e.g., side-channel resistance) is out of scope. For
  tenants with strong isolation needs, run LithOS within fixed MIG partitions.
- Not all CUDA features are equal: certain launch attributes and emerging
  features may change how masks are applied. LithOS tracks stable APIs and
  degrades gracefully when unsure.

Despite these, the common path---DL training loops and inference
graphs---benefits without code changes.

# Conclusion

LithOS treats the GPU like what it has effectively become in modern ML
services: a shared, precious compute fabric that deserves an operating system.
By interposing at the CUDA boundary, learning how long tasks actually take,
slicing kernels to bound preemption latency, and masking TPCs to stack tenants
safely, LithOS delivers the utilization of MPS with the isolation of
MIG---without the rigidity of static partitions.

For practitioners, the upshot is simple:

- If you run latency-critical inference alongside background jobs, you can claw
  back utilization while keeping tail latencies in check.
- If you’re consolidating many small or bursty jobs onto fat GPUs, you can
  spatially stack them at TPC granularity and let LithOS reshape allocations as
  load shifts.
- If your workloads evolve over time, you don’t need per-model
  profiling---LithOS learns online and adapts.

We think this is the right abstraction boundary for the next generation of ML
infrastructure: a GPU OS that balances policy and performance, without changing
how you write CUDA code. The detailed paper dives deeper into mechanisms and
proofs; this post aimed to give you a feel for why these pieces matter and how
they fit together in a real system.
