+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "Sparse Attention That Is Easy to Write and Fast to Serve"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2026-11-02

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Artificial Intelligence", "Systems"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
# Consider these similar to keywords specified for a research paper.
tags = ["sparse attention", "LLM serving", "KV cache", "programming abstractions", "AI agents"]

[extra]
author = {name = "Zhuoming Chen", url = "https://dreaming-panda.github.io/" }
# The committee specification is  a list of objects similar to the author.
committee = [
    {name = "Todd C. Mowry", url = "https://www.toddcmowry.org/"},
    {name = "Tim Dettmers", url = "https://timdettmers.com/"},
    {name = "Zikun Li", url = "https://zikun-li.github.io/"}
]
+++

Large language models are being asked to generate longer and longer
outputs. A reasoning model may think for tens of thousands of tokens
before answering a math problem
([DeepSeek-R1](https://arxiv.org/abs/2501.12948)), and a coding agent may
run for hours. To generate each of those tokens, the model has to look
back over everything that came before, which means reading an
ever-growing amount of saved state from GPU memory. For long
generations, that reading dominates the cost of serving.

_Sparse attention_ is the most direct response: at each step, read only
the parts of the past that matter. It has moved from an academic idea to
a production technique. DeepSeek builds it into its models
([NSA](https://arxiv.org/abs/2502.11089),
[DeepSeek-V3.2](https://arxiv.org/abs/2512.02556)), and dozens of
methods add it to existing models without retraining, such as
[Quest](https://arxiv.org/abs/2406.10774),
[H2O](https://arxiv.org/abs/2306.14048), and
[Double Sparsity](https://arxiv.org/abs/2408.07092).

Yet trying a _new_ sparse attention idea in a realistic setting is
painfully slow. Adding Double Sparsity to the SGLang serving engine takes
roughly 2,000 lines of code, most of which reimplements basic operations
like matrix multiplication and top-k selection for SGLang's memory
layout. Using a standalone research implementation instead does not
help: Quest's original code, despite its optimized kernels, runs 44.4×
slower than SGLang's ordinary full attention, so evaluating an 8B model
on a single math benchmark takes nearly two hours. A sparse attention
algorithm's theoretical savings only become real speedups when it runs
inside a modern serving engine, and getting it there is a substantial
systems project.

This post is about Vortex, a system my collaborators and I built to
remove that bottleneck. In Vortex, a sparse attention algorithm is a few
lines of Python-like code, written as if there were a single request
with a contiguous cache. Vortex turns it into efficient GPU code that
runs inside SGLang, alongside paging, batching, and prefix caching. This
makes iteration fast enough that AI coding agents can do it on their
own. Given Vortex, agents wrote dozens of new sparse attention
algorithms, and an 18-hour autonomous loop found a configuration that
serves a reasoning workload 3.46× faster than full attention at the same
accuracy.

_This post is based on [Vortex](https://arxiv.org/abs/2606.06453), to
appear at NeurIPS 2026, joint work with Xinrui Zhong, Qilong Feng,
Ranajoy Sadhukhan, Yang Zhou, Michael Qizhe Shieh, Zhihao Jia, and Beidi
Chen. The code is
[open source](https://github.com/Infini-AI-Lab/vortex_torch)._

# Why Long Generations Are Expensive

An LLM produces text one token at a time. To generate the next token,
each attention layer compares the newest token's _query_ vector with a
_key_ vector for every earlier token, turns those comparisons into
weights, and takes a weighted average of the earlier tokens' _value_
vectors. Keys and values of past tokens are saved in GPU memory so they
need not be recomputed. This saved state is called the **KV cache**.

The arithmetic per step is small: one query against \\( n \\) keys. But
the entire KV cache must be read from GPU memory at every step, and it
grows with every token generated. GPUs can do arithmetic far faster than
they can read memory, so for long sequences, attention during decoding
is limited by memory traffic rather than computation. Batching many
requests together, the usual trick for keeping a GPU busy, does not fix
this, because each request has its own KV cache to read. As one data
point from our measurements: for an 8B model serving 16 requests with
32K tokens of context each, one dense attention call takes 0.76 ms,
while a sparse version that reads only selected blocks takes 0.025 ms.

Sparse attention works because attention weights are usually
concentrated: a query typically puts most of its weight on a small
fraction of past tokens. If we can cheaply guess which ones, we can read
only those and skip the rest. _Static_ methods choose tokens by
position, for example the first few tokens plus a window of recent ones
([StreamingLLM](https://arxiv.org/abs/2309.17453)). _Dynamic_ methods
choose based on the current query. They tend to be more accurate, but
choosing then becomes part of every decoding step.

<figure id="fig-blocktopk" style="text-align: center;">
<img src="./block-topk.svg" alt="Diagram of block top-k sparse attention. A KV cache is drawn as eight blocks of tokens. Step 1: each block is summarized by its mean key, shown as a dot under each block, computed once. Step 2: at every decode step, each block summary is scored against the query, giving scores 0.12, 0.91, 0.20, 0.05, 0.66, 0.10, 0.31, and 0.83. Steps 3 and 4: the three highest-scoring blocks are kept and exact attention runs over only those blocks to produce the output. The note says each step reads 3 of the 8 blocks plus the small summaries instead of the whole cache." style="width: 100%; height: auto;"/>
<figcaption style="margin-top: 0.5em;"><b>Figure 1</b>: Block top-k attention, the running example in this post. Block summaries are built once; scoring and selection happen at every decoding step.</figcaption>
</figure>

A simple dynamic method, which I will use as a running example, is
**block top-k attention** ([Figure 1](#fig-blocktopk)). Split the KV
cache into blocks of \\( b \\) consecutive tokens and summarize each
block \\( j \\) by its mean key \\( \bar{k}\_j \\). At each step, score
every block against the query \\( q \\), keep the \\( k \\)
highest-scoring blocks \\( I \\), and run ordinary, exact attention over
just the tokens in those blocks:

\\[ s\_j = q \cdot \bar{k}\_j, \qquad I = \operatorname{top-}k\_j (s\_j), \qquad o = \operatorname{softmax}\left( \frac{q K\_I^\top}{\sqrt{d}} \right) V\_I . \\]

Notice that there are two stages. The block summaries depend only on the
keys, so they can be computed once, when a block fills up, and reused at
every later step. Scoring and selection depend on the query, so they run
at every step. Almost every dynamic sparse attention method has this
shape, which mirrors approximate nearest-neighbor search: build a compact
index ahead of time, then query it cheaply. Methods differ in what the
index stores and how it is scored. Quest, for instance, stores each
block's element-wise minimum and maximum keys and uses them to bound
each block's attention score.

# Why New Ideas Are Hard to Deploy

If block top-k is this simple, why does adding a new method to a serving
engine take thousands of lines of code?

The answer lies in how serving engines store the KV cache. Requests have
different lengths, start and finish at different times, and often share
prefixes such as a common system prompt. Giving each request one
contiguous buffer would waste memory, so modern engines use **paged
attention** ([vLLM](https://arxiv.org/abs/2309.06180)): the KV cache
lives in fixed-size pages scattered through GPU memory, and each request
keeps a table listing its pages in order ([Figure 2](#fig-paged)). Pages
can be shared between requests, which is what makes prefix caching
([SGLang](https://arxiv.org/abs/2312.07104)) cheap.

<figure id="fig-paged" style="text-align: center;">
<img src="./paged-layout.png" alt="Comparison of tensor layouts. In a batch layout, three sequences x0, x1, x2 each occupy two adjacent slots in one contiguous buffer. In a paged layout, six pages p0 to p5 sit in shared storage, and a page index table maps sequence x0 to pages 0, 2, 5, sequence x1 to pages 1, 3, 4, and sequence x2 to pages 0, 3, 5. Logically, each sequence is still a row of three pages, but physically the pages are scattered and pages 0, 3, and 5 are shared." style="width: 85%; height: auto;"/>
<figcaption style="margin-top: 0.5em;"><b>Figure 2</b>: In a batch layout (left), each sequence is contiguous. In a paged layout (right), sequences are lists of pages in shared storage, and pages can be shared.</figcaption>
</figure>

This layout breaks the assumption, built into tensor libraries like
PyTorch, that a batch is a contiguous, rectangular array. An algorithm
that takes a few lines of math on paper suddenly needs custom GPU code
for each step: averaging keys within a page, scoring blocks spread
across scattered pages, taking a top-k over a ragged set of blocks.
Existing tools cover only part of this. Attention libraries such as
[FlashInfer](https://flashinfer.ai/2024/02/02/introduce-flashinfer.html)
and [FlexAttention](https://arxiv.org/abs/2412.05496) run attention
efficiently over paged memory once you know which blocks to read. But in
dynamic sparse attention, working out which blocks to read _is_ the
algorithm, and it can cost more than the attention itself. Serving
engines ship a handful of built-in methods with little room for new
ones. Research prototypes with hand-written kernels usually skip paging,
batching, and prefix caching altogether, which is how a sparse method
ends up 44× slower than the dense baseline it was meant to beat.

As a result, the people best placed to invent sparse attention
algorithms, and increasingly the AI agents that could help them, spend
most of their time on systems plumbing.

# Vortex

<figure id="fig-workflow" style="text-align: center;">
<img src="./workflow.png" alt="Workflow diagram. Papers feed into AI agents and researchers, who handle idea generation, analysis, and experimentation. Their algorithms pass through the three layers of Vortex: vFlow, where the algorithm is written as code; vTensor, the tensor abstraction; and the serving system. Measured accuracy and throughput feed back to the agents and researchers." style="max-height: 60vh; width: 70%; height: auto;"/>
<figcaption style="margin-top: 0.5em;"><b>Figure 3</b>: Vortex sits between algorithm designers, human or AI, and the serving system, turning short programs into measured accuracy and throughput.</figcaption>
</figure>

Vortex splits the problem into three layers
([Figure 3](#fig-workflow)): a small language for writing algorithms
(vFlow), a tensor abstraction that understands paged memory (vTensor),
and an execution backend inside SGLang.

## Writing an algorithm: vFlow

In vFlow, a sparse attention method is a Python class with two
functions, one for each stage described above. Here is the complete
block top-k algorithm:

```python
class BlockTopK(vFlow):
    def forward_cache(c):
        c["centroids"] = Mean(c["k"], dim=1)

    def forward_indexer(q, c):
        s = GeMM(c["centroids"], q.T)
        i = topK(Mean(s, dim=2), dim=1)
        return attn(q, c["k"], c["v"], i)
```

`forward_cache` builds the query-independent summaries and stores them
in a named cache entry. `forward_indexer` runs at every decoding step:
it scores the blocks, selects the top-k, and calls attention on the
selected blocks. The key design choice is that the programmer sees a
_single request with contiguous tensors_. Here `c["k"]` looks like an
array of shape (1, blocks, block size, head dimension), even though in
reality it is scattered across pages and shared with other requests in a
batch whose makeup changes at every step. Vortex takes care of the rest.

The same small set of operators (matrix multiplication, reductions,
softmax, top-k, gather, convolution, and a way to carry state from one
step to the next) expresses a wide range of published methods in a few
lines each. Here is the selection logic of Quest:

```python
class Quest(vFlow):
    def forward_cache(c):
        c["max"] = Max(c["k"])
        c["min"] = Min(c["k"])

    def forward_indexer(q, c):
        s = Maximum(q * c["max"], q * c["min"])
        i = topK(Max(Sum(s)))
```

Double Sparsity, the block-selection branch of NSA, and H2O, which
accumulates attention scores across steps, are similarly short. Static
patterns are expressed by building the selected indices from positions
instead of content.

## Running it: vTensor

Underneath, every vFlow variable is a **vTensor**: an ordinary PyTorch
tensor plus layout metadata, namely the batch size, an index-pointer
array marking where each request's data begins, and, for paged data, the
list of pages each request uses. A vTensor operator has a simple
meaning: apply the corresponding PyTorch operation to each request
independently, then stitch the per-request results back into one
batched tensor. For example, `GeMM(c["centroids"], q.T)` becomes "for
each request \\( i \\), multiply its \\( B\_i \\) block summaries by its
query," producing a ragged output whose length differs from request to
request.

The one restriction is that operators may not mix data across requests,
which matches how serving works anyway. In return, the abstraction
composes: the output of any operator is a valid input to the next, with
no layout conversions in between. It also has a pleasant side effect.
Named cache entries like `c["centroids"]` are stored in pages managed by
the same allocator as the KV cache, so features built on paging, such as
prefix caching, keep working without any effort from the algorithm's
author.

## Making it fast

A clean abstraction is only useful if it runs fast. At the start of each
decoding step, the batch size and every sequence length are known, so
Vortex plans the work, balancing GPU thread blocks across requests of
different lengths, and generates kernels from a few templates. Operators
that share a template are fused, so intermediate results such as block
scores never make a round trip through GPU memory.

Top-k selection needed special care, because it is the one step that is
neither a matrix multiplication nor a simple reduction. The standard
radix-based top-k repeatedly buckets values by their digits, and it
slows down sharply when many high scores land in the same bucket. Vortex
adds two tricks. A monotonic remapping of the scores spreads them more
evenly across buckets, and a _stochastic early exit_ stops refining once
it has enough confident winners, sampling the rest from the boundary
bucket. At over 97% recall of the true top-k, the result is 1.30–1.62×
faster than exact radix top-k (1.49× on average).

Finally, Vortex does not reimplement attention itself. It passes the
selected blocks to existing, heavily optimized attention kernels from
FlashInfer and [TensorRT-LLM](https://github.com/NVIDIA/TensorRT-LLM),
inheriting their support for attention variants and low-precision
formats. Where vendor kernels do not support a model's shapes, as with
the latent attention model discussed below, Vortex supplies its own
kernel. The added overhead is small: the summary-building and selection
kernels take a few microseconds, compared with hundreds of microseconds
for dense attention at long contexts.

# What This Makes Possible

## AI agents as sparse attention researchers

If writing a new algorithm takes ten lines and testing it at serving
scale takes minutes rather than days, the cycle of proposing,
implementing, and evaluating ideas becomes cheap enough to hand to an AI
agent. We ran two experiments, both with Qwen3-1.7B on one NVIDIA H200
GPU, measuring accuracy on competition math benchmarks (AMC23 and
AIME24, generating up to 16K tokens) alongside serving throughput. The
agents received Vortex's documentation and eight representative sparse
attention papers.

**One-shot invention.** We asked three agents, Claude Opus 4.7 and
Claude Sonnet 4.6 through
[Claude Code](https://code.claude.com/docs/en/overview) and GPT-5.5
through [Codex](https://developers.openai.com/codex/cli), to each
propose and implement 20 _new_ sparse attention algorithms. All 60
compiled and ran in Vortex without manual fixes. They were also
genuinely different from each other: a structural distance computed from
the programs' syntax trees averaged 0.71–0.79 (out of 1) within each
agent's set. Some ideas were inventive. One scores blocks by how quickly
their relevance is rising, another weights each block's score by the
magnitude of its values, and another smooths scores along the sequence
so that isolated spikes are ignored. All three agents came up with that
last idea independently. After staged filtering, first on a long-context
retrieval benchmark ([RULER](https://arxiv.org/abs/2404.06654)) and then
on the math benchmarks, every agent produced algorithms that match
full-attention accuracy with 2–3.1× higher throughput.

**Long-horizon iteration.** Next, we let Claude Code with Claude Opus
4.7 run an 18-hour autonomous loop on AIME24, free to change anything:
the selection rule, block sizes, the KV cache's numeric format, or which
layers stay dense. Over 23 iterations and 92 submissions
([Figure 4](#fig-agents)), it found a configuration that serves 11,894
tokens per second versus 3,437 for full attention, a 3.46× speedup, at
the same accuracy (38.96% versus 38.54%).

<figure id="fig-agents" style="text-align: center;">
<img src="./agent-generated.png" alt="Scatter plot of accuracy (mean at 16, percent) against throughput in tokens per second for sparse attention algorithms generated by AI agents on AIME24. Full attention sits at about 3,400 tokens per second and 38.5 percent. Many agent-generated points lie to the right at 8,000 to 12,000 tokens per second, several of them at or above full-attention accuracy. Frontier lines for block top-k and Quest are shown for reference; Quest falls off sharply above about 8,500 tokens per second." style="max-height: 60vh; width: 70%; height: auto;"/>
<figcaption style="margin-top: 0.5em;"><b>Figure 4</b>: Each purple point is one sparse attention configuration generated or refined by an AI agent using Vortex (Qwen3-1.7B, AIME24, one H200). The star is full attention.</figcaption>
</figure>

It is worth being clear about what the agent did and did not do. Its
best final algorithms converged back to block top-k, improved through
tuned block sizes, selection strategies, and skipped layers, rather than
a fundamentally new mechanism. Along the way it tested many diverse
ideas, many of which beat full attention. Inventing a fundamentally
better sparse attention algorithm remains an open problem. What Vortex
changes is that an agent can now run dozens of realistic, end-to-end
experiments on its own, which is a prerequisite for getting there.

## Designing for a new architecture

Some of the newest models do not use standard attention at all. DeepSeek
and GLM models use **multi-head latent attention (MLA)**
([DeepSeek-V2](https://arxiv.org/abs/2405.04434)), which compresses each
token's keys and values into a small latent vector plus a separate
component that carries positional information (the rotary embedding,
or "rope"). Existing sparse attention methods were designed for
standard attention, and MLA's compressed layout is exactly the kind of
detail that makes prototyping painful.

With Vortex, we designed a _rope-aware_ block-sparse method for MLA that
scores each block using both the compressed content and the positional
component. On GLM-4.7-Flash
([GLM](https://arxiv.org/abs/2508.06471)), generating up to 32K tokens
for AIME26 problems on one NVIDIA B200 GPU, full attention reaches a
mean accuracy of 0.765 at 1,031 tokens per second. The rope-aware method
comes within about a point (0.752) at roughly 4× the throughput, reaches
up to 4.7× with a tighter block budget, and matches or beats full
attention on pass@4 and pass@8 ([Figure 5](#fig-mla)). Quest stays
behind it throughout. One caveat: the vendor's optimized MLA kernel does
not support this model's head shapes, so the full-attention baseline
falls back to a slower kernel, while the sparse methods run on Vortex's
own MLA kernel. Part of the gap therefore reflects kernel support, not
sparsity alone.

<figure id="fig-mla" style="text-align: center;">
<img src="./mla-glm.png" alt="Plot of accuracy (mean at 16) against throughput for GLM-4.7-Flash on AIME26. Full attention is at 1,031 tokens per second and 0.765 accuracy. The rope-aware sparse method forms a frontier from about 4,100 tokens per second at 0.752 to about 4,900 at 0.685. Quest sits lower, from about 4,050 at 0.735 to 4,350 at 0.677. The rope-unaware variant is far lower, at 0.60 to 0.63." style="max-height: 55vh; width: 60%; height: auto;"/>
<figcaption style="margin-top: 0.5em;"><b>Figure 5</b>: Sparse attention on an MLA model (GLM-4.7-Flash, AIME26, 32K-token generations, one B200). Scoring blocks with the positional component (rope-aware) matters a great deal.</figcaption>
</figure>

The ablation in the same figure is revealing. A _rope-unaware_ variant,
which scores blocks from the compressed content alone, drops to
0.60–0.63 accuracy. The positional component, not just the content,
carries the signal needed to pick the right blocks.

## Learning where the signal lives

That result points to a third use: Vortex as a research instrument.
Because a scoring rule is a few lines of code, we can run controlled
experiments on _which parts_ of the key representation actually drive
block selection.

In Qwen3-4B and Qwen3-8B ([Qwen3](https://arxiv.org/abs/2505.09388)),
we split the 128 query-key channels into eight groups of 16 and masked
one group at a time during block selection, measuring accuracy on RULER
([Figure 6](#fig-channels)). The routing signal turned out to be highly
concentrated: only two groups, g3 and g7, matter. Masking either one
alone barely affects block top-k, although Quest collapses. Masking both
collapses every method to near-random, even with six of the eight groups
intact. Conversely, keeping only the half of the channels that contains
g3 and g7 loses nothing. The same two groups matter at both model sizes,
which suggests a property of the Qwen3 family rather than a quirk of one
model, though we have not checked whether it carries over to other
families.

<figure id="fig-channels" style="text-align: center;">
<img src="./channel-masking.png" alt="Line plot of RULER accuracy for Qwen3-4B when one of eight query-key channel groups, g0 through g7, is masked during block selection. Block top-k and a GQA block variant stay between about 85 and 95 percent for every group. Quest stays between 84 and 92 percent except when g3 is masked, where it drops to about 31 percent, and when g7 is masked, where it drops to about 10 percent." style="max-height: 50vh; width: 55%; height: auto;"/>
<figcaption style="margin-top: 0.5em;"><b>Figure 6</b>: Leave-one-group-out accuracy on RULER for Qwen3-4B. Only channel groups g3 and g7 carry substantial routing signal.</figcaption>
</figure>

## Is it actually fast?

Everything above depends on Vortex delivering real end-to-end speedups,
so we measured them directly against full attention in SGLang, the
engine Vortex is built into. On Qwen3 models from 0.6B to 8B parameters
on an H200, with inputs up to 4K tokens and outputs up to 16K, we swept
the number of blocks each query attends to (the top-k budget) from 256
down to 32 and traced the throughput–accuracy frontier
([Figure 7a](#fig-efficiency)). Allowing up
to 5 points of accuracy loss, block top-k reaches 3.46× (AMC23) and 3.60×
(AIME24) the throughput of full attention, and Quest reaches 2.73× and
2.98×. Under a stricter 1-point budget, block top-k still delivers
2.14–2.31× on AMC23 and 2.42–3.60× on AIME24, depending on model size.

Faster decoding also means lower latency for users under load. With
16K-token prompts arriving at up to 8 requests per second, in a setup
that runs prefill and decoding on separate GPUs to isolate decoding,
sparse attention cuts the 95th-percentile time per output token by up to
11.7× with block top-k and 12.8× with Quest
([Figure 7b](#fig-efficiency)).

<figure id="fig-efficiency" style="text-align: center;">
<img src="./throughput-qwen3-8b.png" alt="Panel (a): accuracy (mean at 32) against throughput for Qwen3-8B on AIME24, with each point labeled by its number of attended blocks. Full attention is at about 1,750 tokens per second and 67.4 percent accuracy. Block top-k runs from 256 blocks at about 3,050 tokens per second and 67.6 percent to 32 blocks at about 6,300 tokens per second and 58.8 percent, staying near full-attention accuracy down to 128 blocks at about 4,250 tokens per second. Quest, labeled with the same budgets, is consistently below block top-k and falls to 51.7 percent at 32 blocks and 5,650 tokens per second." style="width: 75%; height: auto; display: block; margin: 0 auto;"/>
<img src="./latency-qwen3-8b.png" alt="Panel (b): 95th-percentile time per output token in milliseconds against request rate for Qwen3-8B with 16K-token prompts. Full attention rises roughly linearly from about 40 milliseconds at 1 request per second to about 680 at 8. Block top-k and Quest with 160 blocks stay below about 150 milliseconds across the range." style="width: 60%; height: auto; display: block; margin: 1em auto 0;"/>
<figcaption style="margin-top: 0.5em;"><b>Figure 7</b>: Qwen3-8B on one H200. (a) Throughput–accuracy frontiers on AIME24. The number next to each point is its top-k budget, the number of attended blocks of 16 tokens. (b) 95th-percentile time per output token as load increases, with 16K-token prompts and 160 attended blocks.</figcaption>
</figure>

The gains persist at large scale, though they shrink. On MiniMax-M2.7
([MiniMax-M2](https://arxiv.org/abs/2605.26494)), a 229-billion-parameter
mixture-of-experts model served across four B200 GPUs, full attention
reaches 0.83 accuracy at 3,341 tokens per second on AIME26 with
32K-token generations. Block top-k slightly exceeds that accuracy (0.84)
at 1.23× the throughput, and reaches 1.37× with a tighter budget. The
gains are smaller because, at this scale, more of each decoding step
goes to reading model weights and communicating between GPUs rather than
to reading the KV cache.

Across all of these sweeps, one practical default emerged: blocks of 16
tokens with about 125 selected blocks sit near the accuracy ceiling
while keeping most of the speedup.

# Limitations

Vortex currently accelerates only decoding, not the prefill phase that
processes the prompt, and only inference, not training, where sparse
attention would also need a backward pass. It targets attention models
with an explicit KV cache; extending the abstraction to recurrent and
state-space models such as Mamba is future work. And although Vortex
makes experiments cheap, it is not itself an autonomous research system:
our longest agent run refined a known algorithm rather than inventing a
new one.

# Conclusion

Progress in sparse attention has been limited less by ideas than by the
engineering needed to test them where they matter, inside a real serving
engine. Vortex lowers that cost: algorithms are written against a simple
single-request view, and a paged tensor abstraction and an optimized
backend handle everything else. The result makes human researchers
faster, lets AI agents explore the design space on their own, and
doubles as an instrument for understanding why sparse attention works.
As generations grow longer and agents take on more of the research loop,
I expect the ability to turn a ten-line idea into a realistic
measurement within minutes to matter more and more.
