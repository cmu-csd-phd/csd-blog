+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "Operator-Level Disaggregated Serving for Efficient LLM Inference"
date = 2026-05-15

[taxonomies]
areas = ["Artificial Intelligence", "Systems"]
tags = ["LLM serving", "operator disaggregation", "heterogeneous GPUs", "cost modeling"]

[extra]
author = {name = "Zikun Li", url = "https://zikun-li.github.io/" }
committee = [
    {name = "Beidi Chen", url = "https://www.andrew.cmu.edu/user/beidic/"},
    {name = "Tianqi Chen", url = "https://tqchen.com/"},
    {name = "Zhihao Zhang", url = "https://jackfram.github.io/"}
]
+++

<figure id="fig-ods-teaser" style="text-align: center;">
<img src="./ods-vs-colocation.png" alt="A side-by-side comparison of colocated LLM serving, where attention and FFN or MoE operators share one device group, and operator-level disaggregated serving, where the operators run on separate device groups connected by a pipeline." style="max-height: 55vh; width: 90%; height: auto;"/>
<figcaption style="margin-top: 0.5em;"><b>Figure 1</b>: Colocated serving versus heterogeneous operator-level disaggregated serving.</figcaption>
</figure>

# Introduction

Large language model inference demand is rising quickly, and the infrastructure spending required to serve that demand is rising with it. Market analyses and industry reports increasingly point to both substantial present-day serving costs and large projected investment in AI-oriented compute infrastructure. That makes LLM serving an economic problem as much as a systems problem: every generated token consumes scarce accelerator time, memory capacity, and energy. In this setting, even modest improvements in throughput, utilization, or per-token cost can deliver outsized practical benefits. Serving efficiency is therefore no longer a secondary concern behind model quality or training scale. It is becoming a first-order systems problem.

Modern serving systems have responded by specializing different parts of inference. Some systems split prefill from decode, because prefill processes many prompt tokens at once while decode generates one token per request at each step. Multimodal serving systems may split encoder, prefill, and decode work for similar reasons. Cloud serving stacks are also beginning to expose more disaggregated inference workflows. The common pattern is simple: when two pieces of inference stress hardware in different ways, forcing them into one uniform execution path leaves efficiency on the table.

This post looks one level deeper, inside the decode phase itself. Even during decode, not all operators behave alike. Attention has to read from the key-value (KV) cache and is often limited by memory bandwidth and memory capacity. FFN, MoE, and other GEMM-heavy operators are more sensitive to arithmetic throughput and batch size. Yet many serving engines still execute all of these operators together on the same device group. That conventional design is what I will call **colocated serving**.

**Operator-level disaggregated serving (ODS)** separates decode-phase operator groups, such as attention and FFN or MoE, into distinct serving stages instead of executing them as one colocated workload. When those stages are allowed to run on different device types, I will call the design **heterogeneous ODS**. The key promise is hardware matching: put memory-bound attention on hardware that is cost-effective for bandwidth and KV-cache capacity, and put compute-heavy operators on hardware that is cost-effective for FLOPs. The second promise is independent scaling: once attention and GEMM-heavy operators are separated, KV-cache pressure on the attention side no longer directly limits batching on the compute side. [Figure 1](#fig-ods-teaser) sketches this contrast between colocated serving and heterogeneous ODS.

Recent systems suggest that this direction is promising, but there are still two basic questions to answer. First, when does ODS actually reduce cost, and how large can the gain be? Second, are fixed handcrafted splits, such as the attention-FFN disaggregation (AFD) proposed by prior work or attention versus everything else, general enough for modern models? This post takes a theory-first step toward those questions. It builds a small cost model, derives gain bounds for homogeneous and heterogeneous ODS, studies core-attention disaggregation (CAD) as a canonical split, and identifies when CAD fails to realize the idealized cost.

The goal is not to replace detailed profiling or system evaluation. Real serving systems have scheduling overheads, network topology constraints, queueing behavior, and kernel-level details that a compact analytical model will not capture. Instead, the model isolates the mechanisms that determine the cost of ODS: memory pressure from the KV cache, batch-size coupling between attention and GEMM-heavy operators, and the bandwidth-versus-compute profile of the available hardware. This gives us a cleaner way to reason about when a simple split such as CAD should be effective, when its gains are bounded, and why more general serving plans may be needed for modern model architectures.

# Why Colocated Decode Wastes Hardware

Autoregressive decoding produces one token at a time. For each step, every active request runs through the model once and emits one new token. The batch may contain many requests, but each request contributes only one query vector to the attention operator in that step. This makes decode attention very different from prefill attention. Prefill can process a long prompt in a large block. Decode attention repeatedly touches the KV cache while doing relatively little arithmetic per byte loaded.

This leads to the first colocated-serving problem: **poor hardware matching**. During decode, attention is often memory-bandwidth-bound. The operator has to load KV-cache entries from memory, while the amount of computation per loaded byte is low. Tensor cores, which are designed for high-throughput matrix multiplication, can remain severely underutilized during attention execution. [Figure 2](#fig-tensor-core-utilization) shows this underutilization directly.

<figure id="fig-tensor-core-utilization" style="text-align: center;">
<img src="./tensor-core-utilization.png" alt="A plot showing low tensor-core utilization for decode attention on a B200 GPU, illustrating that attention remains far below peak compute utilization even at large batch sizes." style="max-height: 45vh; width: 50%; height: auto;"/>
<figcaption style="margin-top: 0.5em;"><b>Figure 2</b>: Decode attention can leave tensor cores underutilized because it is limited by memory bandwidth rather than arithmetic throughput.</figcaption>
</figure>

The FFN and MoE parts of the model have a different profile. They are dominated by GEMM-like operations and can use tensor cores efficiently when the batch size is large enough. Their problem is not that they are inherently bandwidth-bound; it is that colocated serving can prevent them from reaching the batch size where they become compute-efficient.

That is the second colocated-serving problem: **memory-capacity coupling**. Attention must keep the KV cache on device. As the average sequence length grows, each request occupies more KV-cache memory. Since the same device group also has to hold model weights and activations, longer contexts reduce the number of requests that can fit in a batch. A smaller batch then hurts GEMM-heavy operators, because they may no longer have enough parallel work to saturate the hardware. [Figure 3](#fig-max-batch-size) shows how the feasible batch size falls as sequence length grows.

<figure id="fig-max-batch-size" style="text-align: center;">
<img src="./max-batch-size-vs-seqlen.png" alt="A plot showing that the maximum feasible batch size on an H100 GPU drops as sequence length increases, because longer contexts consume more KV-cache memory." style="max-height: 45vh; width: 50%; height: auto;"/>
<figcaption style="margin-top: 0.5em;"><b>Figure 3</b>: KV-cache growth reduces feasible batch size as context length increases.</figcaption>
</figure>

These two effects reinforce each other. Attention is bandwidth-sensitive even when the batch is large. GEMM-heavy operators want larger batches, but attention's KV cache consumes the memory that would otherwise support those batches. A colocated device group therefore has to serve operators with different bottlenecks under one shared memory and hardware budget.

# What Operator-Level Disaggregation Changes

ODS changes the serving layout by letting different operator groups run as different stages. In the simplest attention-versus-rest design, the attention stage stores KV cache and handles the memory-bound attention computation, while the rest stage stores model weights and handles GEMM-heavy work. Activations move between stages through a pipeline.

This separation creates two degrees of freedom.

First, it enables **hardware matching**. If one available GPU type has better memory bandwidth per dollar and another has better compute throughput per dollar, a colocated deployment must choose one type for both attention and GEMM-heavy work. Heterogeneous ODS can choose separately: attention goes to the bandwidth-efficient side, while FFN, MoE, and projections go to the compute-efficient side.

Second, it enables **independent scaling**. In colocated serving, attention KV-cache memory and GEMM batch size are tied together because they share the same device memory. In ODS, the attention side can scale according to KV-cache needs, while the compute side can aggregate work from multiple attention-side workers and maintain a larger effective batch. This is what lets the GEMM side remain in a compute-efficient regime even when long contexts would force a colocated system into a small batch.

ODS does introduce communication: tensors have to move between stages. The analysis here treats communication as overlapped with computation through micro-batching and pipelining, so the cost model focuses on GPU computation cost. This idealization isolates the main question: if communication can be hidden, what is the structural cost benefit of separating operator classes?

This framing also explains why ODS is different from simply adding more GPUs to a colocated deployment. More colocated replicas increase total throughput, but each replica still carries the same internal coupling between KV-cache memory and GEMM batch size. ODS changes the shape of the work inside a decoding step. It lets the system provision attention capacity and compute capacity separately, and it lets different hardware types participate according to their strengths.

# A Lightweight Cost Model

The model deliberately uses a small set of hardware parameters. A GPU type is summarized by its unit-time cost \\(c\\), memory bandwidth \\(\beta\\), memory capacity \\(M\\), and peak compute throughput \\(F\\). For each operator \\(o_i\\), let \\(D_i(b)\\) be the bytes it loads at batch size \\(b\\), and let \\(W_i(b)\\) be the number of floating-point operations it performs.

The latency model is the roofline intuition:

$$
T(o_i) = \max\left( D_i(b) / \beta, W_i(b) / F \right).
$$

The first term is time spent moving data from memory. The second is time spent doing arithmetic. The slower side determines the operator latency. Multiplying latency by unit-time cost gives the monetary cost of running the operator on that GPU.

For the rest of the analysis, operators are grouped into attention and GEMM-heavy work. This is not because other operators do not exist, but because attention and GEMM dominate the decode cost structure. Let \\(D^{\mathrm{attn}}(b)\\) be the total memory traffic of the attention operators, \\(D^{\mathrm{gemm}}(b)\\) be the total memory traffic of the GEMM-heavy operators, and \\(W^{\mathrm{gemm}}(b)\\) be the total arithmetic work of the GEMM-heavy operators. Attention is modeled as memory-bound. GEMM is modeled as compute-bound once the batch size is large enough.

In colocated serving, attention and GEMM-heavy operators run on the same GPU type and share the same feasible batch size. Attention contributes its bandwidth-limited term, while GEMM must keep the roofline maximum because a small colocated batch may fail to saturate compute:

$$
\mathrm{CPT}^{\mathrm{coloc}} =
\frac{c}{b}\left(
  \frac{D^{\mathrm{attn}}(b)}{\beta}
  +
  \max\left(
    \frac{D^{\mathrm{gemm}}(b)}{\beta},
    \frac{W^{\mathrm{gemm}}(b)}{F}
  \right)
\right).
$$

For colocated serving, the important extra constraint is memory capacity. If model weights use \\(M_{\mathrm{weights}}\\) bytes and each request uses \\(m_{\mathrm{kv}}(s)\\) bytes of KV cache at average sequence length \\(s\\), then the feasible batch size is bounded by

$$
b_{\max}(s) =
\left\lfloor
  \frac{M - M_{\mathrm{weights}}}{m_{\mathrm{kv}}(s)}
\right\rfloor.
$$

As \\(s\\) grows, the KV cache grows, and \\(b_{\max}(s)\\) shrinks. Once that batch size falls below the GEMM compute-bound threshold, the max in the colocated expression is governed by memory traffic instead of arithmetic throughput, and colocated GEMM becomes inefficient.

In a homogeneous ODS deployment, both stages use the same GPU type, but attention and GEMM no longer share one memory budget. Under the idealized regime where the GEMM side can keep a sufficiently large batch, attention runs at bandwidth cost and GEMM runs at compute cost:

$$
\mathrm{CPT}^{\mathrm{hom}} =
\frac{c}{b}\left(
  \frac{D^{\mathrm{attn}}(b)}{\beta}
  +
  \frac{W^{\mathrm{gemm}}(b)}{F}
\right).
$$

The difference from colocated serving is the missing GEMM roofline maximum. Homogeneous ODS does not need different hardware to help; it helps when separating the memory budgets lets the GEMM-heavy side remain in the compute-efficient regime that colocation loses at long contexts.

In a heterogeneous ODS deployment, attention and GEMM can use different GPU types. The cost-per-token expression further exposes the hardware-matching idea:

$$
\mathrm{CPT}^{\mathrm{het}} =
\frac{1}{b}\left(
  \frac{D^{\mathrm{attn}}(b)}{\beta_1} c_1
  +
  \frac{W^{\mathrm{gemm}}(b)}{F_2} c_2
\right).
$$

The attention side depends on cost per byte, \\(c_1 / \beta_1\\). The GEMM side depends on cost per FLOP, \\(c_2 / F_2\\). A single homogeneous deployment cannot optimize both terms independently when different GPU types have different bandwidth-to-compute tradeoffs.

This is the main simplification that makes the later results interpretable. Attention cost grows with the amount of KV cache that must be read. GEMM work grows with the number of model parameters and the batch size. In colocated serving, the feasible batch size is itself controlled by KV-cache memory. ODS breaks that dependency by moving the KV cache and the GEMM-heavy work to different stages.

# What The Model Predicts

<div style="background: #f7f7f7; border: 1px solid #d6d6d6; border-radius: 4px; padding: 0.8em 0.95em; margin: 1.25em 0; font-size: 0.95em; line-height: 1.5;">
<div style="font-weight: 700; margin-bottom: 0.3em;">Insight 1: Homogeneous ODS helps only after KV-cache pressure constrains colocated batching.</div>
<div>When colocated GEMM already reaches compute-bound execution, homogeneous ODS has no modeled cost advantage. The gain appears once KV-cache growth pushes \(b_{\max}(s)\) below the GEMM compute-bound threshold, because disaggregation lets the GEMM side keep a larger effective batch. The gain increases with sequence length but remains bounded by \(G_{\mathrm{hom}}(s) < M/(M - M_{\mathrm{weights}})\).</div>
</div>

The first result asks what homogeneous ODS gains over colocated serving. This isolates the benefit of disaggregation itself, without relying on heterogeneous hardware. The answer is conditional: there is no benefit when sequences are short enough that colocated GEMM is already compute-bound. In that regime, the colocated system and the disaggregated system are both operating GEMM efficiently, so separating the operators does not reduce the modeled cost.

The gain appears when sequence length grows enough that KV-cache pressure pushes the colocated batch below the GEMM compute-bound threshold. At that point, the colocated system pays the cost of reloading model weights without enough batch parallelism to amortize the work. ODS removes the KV-cache pressure from the GEMM side, allowing the compute-heavy stage to stay in its efficient regime.

This prediction pushes against a simplistic "disaggregation is always better" story. For short contexts or small models, the colocated system may already be close to the modeled optimum. In those cases, ODS adds architectural complexity without changing the dominant cost. The model instead points to the workloads where ODS should be evaluated most seriously: long-context serving, large models, and configurations where model weights and KV cache compete for a tight memory budget.

The model also says that this homogeneous gain is bounded. The bound depends on how much of GPU memory is occupied by model weights:

$$
G_{\mathrm{hom}}(s) < \frac{M}{M - M_{\mathrm{weights}}}.
$$

The bound is a sanity check. If weights occupy only a small part of device memory, then the KV cache has plenty of room and disaggregation cannot help much through batch-size decoupling. If weights occupy most of memory, the colocated system is much more constrained, and disaggregation has more room to help. [Figure 4](#fig-homo-gain) visualizes both the long-context gain and the upper-bound behavior.

<figure id="fig-homo-gain" style="text-align: center;">
<img src="./homogeneous-ods-gain.png" alt="Curves showing the theoretical cost gain of homogeneous operator-level disaggregation over colocated serving, with gain increasing at longer sequence lengths and approaching an upper bound." style="max-height: 48vh; width: 90%; height: auto;"/>
<figcaption style="margin-top: 0.5em;"><b>Figure 4</b>: Homogeneous ODS helps once long contexts make colocated GEMM batch sizes too small.</figcaption>
</figure>

<div style="background: #f7f7f7; border: 1px solid #d6d6d6; border-radius: 4px; padding: 0.8em 0.95em; margin: 1.25em 0; font-size: 0.95em; line-height: 1.5;">
<div style="font-weight: 700; margin-bottom: 0.3em;">Insight 2: Heterogeneous ODS helps when no one GPU type is best for both attention and GEMM.</div>
<div>Heterogeneous ODS adds value when one GPU type is more cost-effective for memory bandwidth and another is more cost-effective for arithmetic throughput. The gain is unimodal in sequence length: small when GEMM dominates, small again when attention dominates, and largest when both matter. It is bounded by \(G_{\mathrm{het}}(s) \leq (1 + \sqrt{\eta})/2\), where \(\eta = \beta_1 F_2 / (\beta_2 F_1)\).</div>
</div>

The second result asks what heterogeneous ODS gains over homogeneous ODS. Here the benefit does not come from separating memory budgets alone; it comes from assigning each operator class to the GPU type that best matches it. The model defines two cost-efficiency metrics for each GPU type: cost per byte, \\(\alpha_j = c_j / \beta_j\\), and cost per FLOP, \\(\gamma_j = c_j / F_j\\). Heterogeneous ODS matters when no single GPU type is best on both metrics.

The shape of the gain is also informative. At very short sequence lengths, the workload is GEMM-dominated, so the best homogeneous GPU is already the compute-efficient choice. At very long sequence lengths, the workload is attention-dominated, so the best homogeneous GPU is already the bandwidth-efficient choice. Heterogeneity helps most in the middle, when attention and GEMM both matter enough that choosing one GPU type for everything is a compromise.

The upper bound depends on the hardware specification ratio

$$
\eta = \frac{\beta_1 F_2}{\beta_2 F_1}.
$$

This ratio captures how different the two GPU types are in bandwidth-versus-compute profile. The resulting bound is

$$
G_{\mathrm{het}}(s) \leq \frac{1 + \sqrt{\eta}}{2}.
$$

If the two GPU types have similar bandwidth-to-compute profiles, then \\(\eta\\) is close to 1 and heterogeneous assignment has little to exploit. If their profiles are very different, the possible benefit is larger. [Figure 5](#fig-hetero-gain) illustrates this by comparing the best homogeneous choice with heterogeneous placement across sequence lengths.

<figure id="fig-hetero-gain" style="text-align: center;">
<img src="./heterogeneous-ods-gain.png" alt="Plots comparing homogeneous and heterogeneous operator-level disaggregated serving, showing that heterogeneous placement follows the lower cost envelope and has a peak gain at intermediate sequence lengths." style="max-height: 48vh; width: 90%; height: auto;"/>
<figcaption style="margin-top: 0.5em;"><b>Figure 5</b>: Heterogeneous ODS helps most when the workload is balanced between attention and GEMM-heavy operators.</figcaption>
</figure>

Together, these two results give a compact rule of thumb. ODS is most attractive for large models, memory-constrained deployments, and long-context workloads where colocated batching becomes tight. Heterogeneous ODS is most attractive when the available hardware types differ meaningfully in memory-bandwidth efficiency versus compute efficiency.

The bounds also set expectations. They do not say that every implementation will reach the bound. They say that, under the assumptions of the model, the gain cannot grow arbitrarily just because sequence length grows or because two GPU types are available. That matters for system design: once the bound is modest for a given deployment, the planner and runtime have less headroom to justify complexity. When the bound is large, it signals that careful operator placement is worth the engineering effort.

# CAD: A Simple Split

The simplest concrete ODS policy is **core-attention disaggregation (CAD)**. CAD places all attention operators on one device group and all remaining operators on another. In the simplified cost model, this split is enough to realize the ideal disaggregated cost: attention runs at bandwidth cost, GEMM-heavy work runs at compute cost, and the two sides can be provisioned so that neither side sits idle.

<div style="background: #f7f7f7; border: 1px solid #d6d6d6; border-radius: 4px; padding: 0.8em 0.95em; margin: 1.25em 0; font-size: 0.95em; line-height: 1.5;">
<div style="font-weight: 700; margin-bottom: 0.3em;">Insight 3: CAD is the canonical split that realizes the idealized ODS cost.</div>
<div>Under the simplified model, CAD attains the ideal disaggregated cost by placing attention on one side and all remaining operators on the other. Attention pays bandwidth cost, GEMM-heavy work pays compute cost, and the two sides can be provisioned so neither waits. This ideal is achieved only when the pipeline can be balanced and communication is hidden.</div>
</div>

[Figure 6](#fig-cad) shows this CAD pipeline structure.

<figure id="fig-cad" style="text-align: center;">
<img src="./cad-pipeline.png" alt="A diagram of core-attention disaggregation, with attention operators assigned to one device group and the remaining operators assigned to another, plus a pipelined schedule across micro-batches." style="max-height: 55vh; width: 90%; height: auto;"/>
<figcaption style="margin-top: 0.5em;"><b>Figure 6</b>: CAD separates attention from the rest of the decode computation.</figcaption>
</figure>

Why is such a simple split meaningful? Under the model's assumptions, the operator classes are cleanly separated by bottleneck. Attention is the memory-bound KV-cache reader. The remaining GEMM-heavy operators are the compute-bound matrix multiplications once the batch size is sufficient. CAD assigns each class to the side that suits it. It also removes the memory-capacity coupling that makes the colocated GEMM side inefficient at long contexts.

This does not mean CAD is universally optimal in a real system. It means that CAD gives us a baseline for understanding the best-case version of ODS. If the model is uniform, if stage latencies can be balanced, and if communication is hidden, CAD can match the idealized cost predicted by the model. The interesting question is what breaks when those assumptions stop holding.

# Where CAD Breaks

<div style="background: #f7f7f7; border: 1px solid #d6d6d6; border-radius: 4px; padding: 0.8em 0.95em; margin: 1.25em 0; font-size: 0.95em; line-height: 1.5;">
<div style="font-weight: 700; margin-bottom: 0.3em;">Insight 4: CAD can fail when stage-latency ranges do not overlap.</div>
<div>A balanced CAD pipeline needs an operating point where the attention-side latency and rest-of-model latency match. Each side can vary latency only within a feasible range determined by memory capacity, bandwidth, model-weight loading, and batch size. If the two ranges do not overlap, no micro-batch size or provisioning choice can remove the resulting pipeline bubbles.</div>
</div>

The first failure mode is **feasibility mismatch**. A balanced CAD pipeline needs the attention side and the rest-of-model side to have matching stage latencies. In practice, each side can only vary its latency within a bounded range. The attention stage is constrained by memory capacity and bandwidth, especially because concurrent micro-batches and attention stages share available KV-cache memory. The rest stage has a lower bound from loading model weights, and its latency grows with batch size as GEMM compute increases.

For CAD to run without bubbles, these feasible latency ranges have to overlap. If they do, there is an operating point where the two stages advance together. If they do not, no choice of micro-batch size or provisioning can fully equalize the stages, and the faster side waits. [Figure 7](#fig-cad-feasibility) illustrates the difference between overlapping and non-overlapping latency ranges.

<figure id="fig-cad-feasibility" style="text-align: center;">
<img src="./cad-feasibility.png" alt="A diagram showing two CAD pipeline feasibility cases: one where attention and rest-stage latency ranges overlap, and one where the ranges are separated and cannot be balanced." style="max-height: 48vh; width: 90%; height: auto;"/>
<figcaption style="margin-top: 0.5em;"><b>Figure 7</b>: CAD only realizes the idealized cost when the stage latency ranges can be balanced.</figcaption>
</figure>

<div style="background: #f7f7f7; border: 1px solid #d6d6d6; border-radius: 4px; padding: 0.8em 0.95em; margin: 1.25em 0; font-size: 0.95em; line-height: 1.5;">
<div style="font-weight: 700; margin-bottom: 0.3em;">Insight 5: Hybrid-attention variation can make one fixed CAD split imbalanced.</div>
<div>Hybrid-attention models can mix full-attention layers, whose latency grows with sequence length, and efficient-attention layers, whose latency is much smaller. A single attention-versus-rest split may match one layer type but not the other: tuning the rest stage for full attention leaves bubbles on efficient-attention layers, while tuning it for efficient attention makes full-attention layers the bottleneck.</div>
</div>

The second failure mode is **hybrid-attention variation**. The simplified CAD story assumes that every attention layer has roughly the same attention pattern and therefore similar latency. Many modern models violate this assumption. A hybrid-attention model may mix full-attention layers with efficient-attention layers such as sliding-window attention. Full attention reads the full context and grows with sequence length. Sliding-window attention reads a bounded local window and can be much faster.

Under CAD, both types of attention are placed on the same attention-side stage, while the rest-of-model stage has a more fixed per-layer latency. If the rest stage is tuned to match full attention, it is too slow for efficient-attention layers and the attention side waits. If it is tuned to match efficient attention, full-attention layers become the bottleneck and the rest side waits. A single attention-versus-rest split cannot simultaneously balance both, as shown in [Figure 8](#fig-imbalanced-cad).

<figure id="fig-imbalanced-cad" style="text-align: center;">
<img src="./imbalanced-cad.png" alt="A pipeline schedule for a hybrid-attention model showing short efficient-attention stages, long full-attention stages, and idle bubbles when CAD uses one fixed attention-versus-rest split." style="max-height: 50vh; width: 90%; height: auto;"/>
<figcaption style="margin-top: 0.5em;"><b>Figure 8</b>: Hybrid-attention variation can introduce unavoidable bubbles under a fixed CAD split.</figcaption>
</figure>

This is the key reason CAD should be viewed as a canonical split, not the final answer. It explains the idealized benefit of separating attention from GEMM-heavy work, but it also exposes why more general serving-plan formulations are needed.

# What Comes Next

The analysis leaves three practical questions for future systems work.

First, how should we represent the full ODS decision space? A complete plan includes operator partition boundaries, device assignment, tensor-parallel and expert-parallel configurations, number of micro-batches, micro-batch sizes, and the pipeline schedule. CAD fixes the partition to attention versus everything else. A more general formulation needs to include CAD as one point while allowing richer partitions when the model structure demands them.

Second, how should the planner handle hybrid-attention models? If attention behavior varies across layers, a layer-by-layer partition may be too flexible and expensive to search, while a single global CAD partition may be too rigid. One promising direction is to exploit repeated structure in the model by grouping recurring layer patterns and searching over those groups.

Third, how should cost minimization interact with real deployment constraints? A practical serving plan has to minimize cost per token while satisfying latency service objectives and fitting a fixed inventory of GPU types. That makes the problem a constrained optimization problem over both continuous choices, such as batch size, and discrete choices, such as partition and device mapping. [Figure 9](#fig-system-overview) sketches how these inputs could feed into a planner and runtime.

<figure id="fig-system-overview" style="text-align: center;">
<img src="./system-overview.png" alt="An envisioned operator-level disaggregated serving architecture where a planner takes model, hardware, profiling, workload, and SLO inputs and produces a serving plan that a runtime executes across heterogeneous device groups." style="max-height: 48vh; width: 60%; height: auto;"/>
<figcaption style="margin-top: 0.5em;"><b>Figure 9</b>: An envisioned path from the analysis to a planner and runtime for operator-level disaggregated serving.</figcaption>
</figure>

The point is not to claim that all of this has been solved. It is to clarify the structure of the problem. ODS helps by breaking a harmful coupling between attention and GEMM-heavy operators. Heterogeneous ODS adds another lever when hardware types have complementary cost profiles. CAD shows the cleanest version of the idea, and its failure modes show why a general planner and runtime need to reason about more than a fixed attention-versus-rest split.

That is the broader takeaway. Operator-level disaggregation is not just a placement trick. It is a way to expose the different resource profiles already present inside decode. The theory gives a compact language for discussing when that exposure should reduce cost, and the CAD failure modes show where the next layer of system work has to begin.
