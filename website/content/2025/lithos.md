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

## TL;DR

LithOS reclaims GPU scheduling in software. It interposes on CUDA (virtual streams), predicts runtimes online, slices kernels (~500 μs) to bound preemption, and applies per-launch TPC masks for fine-grained spatial stacking to keep devices busy and protect tail latencies—no app changes.

# Introduction

GPUs are expensive---and too often idle. Inference bursts and copy-heavy phases in training leave gaps in time, while small or bursty jobs underfill big devices in space. For instance, an LLM inference service with a p95 target under 30 ms may need to share a GPU with a background training job: today, you either strand capacity (MIG/time slicing) or risk tails exploding (MPS). LithOS aims to combine near-MPS utilization with MIG-like isolation, without changing your CUDA code.

Two tensions drive this space:
- Latency vs. throughput within a tenant (small slices preempt faster, big slices run more efficiently).
- Utilization vs. isolation across tenants (packing keeps devices busy, partitioning prevents interference).
LithOS addresses both with just-in-time slicing in time and fine-grained masking in space.

This post focuses on NVIDIA hardware and terminology. The default sharing
mechanism is time slicing (TS): the device switches application contexts roughly every few
hundred microseconds, and if one app idles, the next runs immediately. Time
slicing is simple and fair---each context gets a proportional share---but
it neither supports spatial stacking nor accounts for diverse requirements.
Prior work (e.g., [TGS](https://www.usenix.org/conference/osdi22/presentation/han), [REEF](https://www.usenix.org/conference/nsdi23/presentation/wu)) adds priority to temper "fairness" with service
goals, but cannot overcome the limits of coarse temporal multiplexing alone.

Spatial partitioning helps on ever-larger GPUs. With [Multi-Instance GPU (MIG)](https://docs.nvidia.com/datacenter/tesla/mig-user-guide/), users carve a device into a few instances (at GPC granularity) and hand those to apps. MIG provides isolation, but the units are coarse and reconfiguration takes ~1s---too slow for interactive or shifting workloads.

At the other end, NVIDIA’s [Multi-Process Service (MPS)](https://docs.nvidia.com/deploy/mps/index.html) maximizes utilization by collapsing tenants into a single hardware context. This keeps the device busy but offers little policy: the app that launches more work tends to win. Systems like [Orion](https://doi.org/10.1145/3627703.3629578) and MPS client priority mitigate this by buffering and prioritizing launches, yet inherit MPS's lack of fine-grained time/space control.

What's missing is a GPU "operating system" that unifies software control over time and space so the device stays busy without sacrificing predictability.

The core barriers are: (1) you can’t preempt arbitrary GPU kernels at fine granularity, and (2) MIG’s coarse spatial units make dynamic partitioning impractical. LithOS addresses both in software.

LithOS is our attempt to reconcile these goals with a principled, OS-like
approach to GPUs. The key idea is to pull scheduling decisions back into
software, where we can apply policy, while still feeding the device enough work
to keep it saturated. LithOS interposes application submissions, understands
dependencies, estimates task durations online, and enforces fine-grained time
and space partitioning at sub-millisecond and sub-GPC granularity---without
requiring application changes.

At a glance, LithOS contributes:

- Virtual streams: reclaim launch control from the device scheduler while preserving application concurrency.
- Online latency micro-models: predict per-task runtime and scale predictions with assigned compute share.
- Transparent kernel slicing: bound preemption latency to hundreds of microseconds with negligible overhead on common kernels.
- Per-launch TPC masking: enable fine-grained spatial stacking for simultaneous, isolated execution.
- SLO-friendly scheduling: priority, fairness, and tail-aware admission at slice granularity.

The rest of this post dives into how these pieces fit together and what they
buy you in practice.

# Design

![LithOS design: virtual streams, online runtime prediction, kernel slicing, and per-launch TPC masking.](design.pdf)

_Figure: LithOS interposes on CUDA submissions, predicts runtimes online, slices kernels, and applies per-launch TPC masks to realize policy on hardware._

 

LithOS interposes the CUDA API, buffers GPU tasks, and performs scheduling normally left to the device. The key difference is integrating four pieces—virtual streams, a tiny latency model, slicing, and TPC masking—to get MPS-like utilization with MIG-like isolation.

## Reclaiming GPU Scheduling with Virtual Streams

CUDA apps flood the device with copies and kernels, which is great for a single tenant but problematic when many share a GPU: the hardware scheduler is throughput-first. LithOS intercepts submissions into software queues (“virtual streams”), maintains only a bounded amount of outstanding work, and has a daemon issue operations while respecting dependencies.

Keeping a small cushion of ready work per physical stream keeps the GPU fed; bounding the cushion lets LithOS throttle or admit slices to meet SLOs. LithOS preserves intra-app concurrency by tracking events and stream order, mapping many virtual streams onto a few physical streams—like multiplexing threads onto cores. Policy hooks live on these queues: high-priority services get larger budgets and immediate admission for latency-critical slices; best-effort work drains opportunistically.

## Cheaply Estimating Task Durations

To keep the device busy yet preempt quickly, LithOS must know “how long will this take if I give it k TPCs now?” ML workloads are repetitive (training loops, repeated inference graphs), so we learn from recent launches.

LithOS maintains per-(kernel, shape) micro-models keyed by salient launch parameters and aggregates recent durations (robust medians). To predict across spatial shares, we use a tiny transformed-Amdahl model:

$$
t(p) \approx t_\text{serial} + t_\text{parallel} / f(p)
$$

Here, p is the assigned TPC count and f(p) captures sublinear scaling. A tiny online regression updates t_serial and t_parallel from observed slices. The scheduler asks: “If I give this app k TPCs for the next 2 ms, how much of its queue clears?” Those forecasts drive admission and the outstanding-work cushion. No offline profiling; we weight recent data and fall back to conservative caps for unseen kernels.

## Slicing Grids for Fine-grained Scheduling in Time

![Slicing enables optimal scheduling by bounding preemption latency with short kernel slices.](slicing.pdf)

_Figure: LithOS slices kernels into ~500 μs chunks to bound preemption latency while keeping the GPU fed._

To bound preemption latency, LithOS slices kernels. Kernels launch as grids of blocks; we transparently split a grid into multiple launches, each covering a subset of blocks. The latency model picks a ~500 μs quantum: large enough to amortize <10 μs launch overhead, small enough to preempt LC work quickly. Many kernels already fit and need no slicing.

Edge cases: (1) persistent/cooperative kernels that need all blocks resident shouldn’t be sliced; (2) tiny kernels under the quantum are left intact. Because slicing happens at submission time, apps require no code changes.

## Masking TPCs for Fine-grained Scheduling in Space

LithOS stacks applications spatially by masking TPCs per launch, enabling simultaneous execution on disjoint SM subsets. We treat TPCs as the maskable unit; on modern NVIDIA GPUs, a TPC maps to a set of SM resources that can be selectively enabled.

The latency model already predicts across TPC shares, so policy can reshape space on the fly: e.g., give 1/3 of TPCs to LC work for 1 ms while a training job streams on the rest; when the LC queue drains, the BE job expands—no MIG reconfig needed.

## Compatibility, safety, and deployment

LithOS is a drop-in for most CUDA apps. Caveats:
- Cooperative/persistent kernels and device-side launches may restrict slicing.
- No device-memory oversubscription; we can meter allocation-heavy phases.
- For hard security isolation, pair LithOS with fixed MIG partitions; LithOS then adds dynamic share reshaping inside the partition.

# Results

We implemented LithOS in about 5000 lines of code and evaluated it along two metrics for a set of neural network models.
We compare LithOS to time slicing, MPS, and MIG, as well as three other
state-of-the-art systems, [REEF](https://www.usenix.org/conference/nsdi23/presentation/wu), [TGS](https://www.usenix.org/conference/osdi22/presentation/han), and [Orion](https://doi.org/10.1145/3627703.3629578).

We stack three applications together, a high-priority service (HP A), a
closed-loop high-priority job (HP B), and a best-effort job (BE). We also refer to latency-critical (LC) slices within HP/BE workloads when meeting service-level objectives (SLOs).

GPU sharing should both maximize GPU utilization and fulfill application SLOs.
System throughput is a good proxy metric for GPU utilization. Application SLOs
are measured via the tail of latency distributions (e.g., 99th percentile) for
LC services and completion time/throughput for HP/BE jobs. We report both ends
of this trade-off and show that LithOS improves the Pareto frontier relative to
prior mechanisms.

Our evaluation uses representative neural-network workloads (compute- and memory-bound), with steady-state training and bursty inference. We compare on modern NVIDIA datacenter GPUs against: (1) time slicing (TS), (2) MPS, (3) MIG partitions, and (4) [REEF](https://www.usenix.org/conference/nsdi23/presentation/wu), [TGS](https://www.usenix.org/conference/osdi22/presentation/han), and [Orion](https://doi.org/10.1145/3627703.3629578), all using the same binaries.

## Pushing the Pareto Frontier

![LithOS provides the utilization of MPS with the isolation of MIG.](
  trade-off.pdf)

_Figure: LithOS keeps throughput near MPS while tracking SLO attainment close to isolated baselines by dynamically reshaping time/space allocations._

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

## Allocating Performance

![LithOS services critical applications while allowing best-effort execution.](
  goodput.pdf)

_Figure: LC meets SLOs while HP and BE utilize remaining TPCs; BE yields quickly during LC spikes and ramps back smoothly afterward._

How does LithOS push the latency/throughput Pareto frontier? Similar to partitioning systems like MIG and TS, it isolates HP A from the noisy neighbors that plague MPS-like sharing. But unlike static partitions, it doesn’t strand capacity. In mixed LC/HP/BE experiments, LithOS maintains LC
SLOs and assigns the remaining TPCs to HP and BE jobs. When LC traffic spikes,
BE yields quickly (sub-millisecond) and HP absorbs a controlled slowdown; when
traffic subsides, BE ramps back up without handoffs or instance churn.

We call this goodput-aware allocation: best-effort work only runs when it
won't jeopardize SLOs.

## Successfully Limiting Tail Latencies

![LithOS successfully limits tail latencies by preventing interference.](
  latency.pdf)

_Figure: Tail latencies shrink due to bounded preemption latency and spatial masking during LC bursts._

Without partitioning, sharing systems are unable to limit tail latencies. These diverge on MPS, priority, [REEF](https://www.usenix.org/conference/nsdi23/presentation/wu), and [Orion](https://doi.org/10.1145/3627703.3629578). Temporal partitioning systems limit this to some extent. LithOS keeps latencies close to isolated execution and is the only system that meets all SLOs. Specifically, LithOS reduces tail latencies 13× vs. MPS and 12× vs. [Orion](https://doi.org/10.1145/3627703.3629578).

Why do tails shrink? Two reasons:
- Bounded preemption latency from slicing: LC work isn’t stuck behind multi-millisecond kernels.
- Spatial masking during LC bursts: LC kernels run on a clean subset of TPCs, reducing queueing and cache pollution.
If a kernel cannot be sliced safely or a mask is risky, LithOS falls back to temporal sharing while keeping admission control.

## Methodological notes

We evaluate steady state (minutes), average across runs with confidence bands, and pin CUDA versions for fairness. Results focus on relative deltas; trends are robust: just-in-time scheduling plus sub-millisecond slicing and fine-grained spatial partitioning improves the latency–throughput trade-off.

# Limitations and what we don’t (yet) do

Like any OS, LithOS makes trade-offs:
- Cooperative/persistent kernels constrain slicing.
- Collectives and multi-GPU jobs can amplify tails across devices; LithOS can’t remove global barriers.
- No device-memory paging; use model parallelism/checkpointing when memory-bound.
- Hard security isolation is out of scope; use MIG for that, with LithOS inside.
- Some CUDA features may affect masking; we track stable APIs and degrade gracefully.

Despite these, the common path—DL training loops and inference graphs—benefits without code changes.

# Conclusion

LithOS treats the GPU as a shared compute fabric that deserves an operating system. By interposing at the CUDA boundary, learning task times, slicing to bound preemption, and masking TPCs to stack tenants, LithOS delivers MPS-like utilization with MIG-like isolation—without rigid partitions.

For practitioners:
- Run LC inference next to background jobs and claw back utilization while keeping tails in check.
- Consolidate many small/bursty jobs by stacking at TPC granularity; LithOS reshapes shares as load shifts.
- Skip per-model profiling—LithOS learns online and adapts.

We believe this is the right abstraction boundary for the next generation of ML infrastructure: a GPU OS that balances policy with performance, without changing CUDA code.
