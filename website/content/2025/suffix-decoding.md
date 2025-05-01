+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "SuffixDecoding: Model-Free Acceleration for LLM Inference"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2025-05-01

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Systems", "Artificial Intelligence"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
# Consider these similar to keywords specified for a research paper.
tags = ["llm serving", "speculative decoding"]

[extra]
author = {name = "Gabriele Oliaro", url = "https://www.gabrieleoliaro.com" }
# The committee specification is  a list of objects similar to the author.
committee = [
    {name = "Graham Neubig", url = "https://www.phontron.com/"},
    {name = "Tianqi Chen", url = "https://tqchen.com/"},
    {name = "Ruihang Lai", url = "https://ruihanglai.com/"}
]
+++


Snowflake has recently unveiled ArcticInference, the fastest speculative decoding solution for vLLM currently available. ArcticInference can reduce the end-to-end latency for **LLM agent tasks** by as much as **4x** and can enhance **open-ended chat completion** workloads by up to **2.8x**.

![Speedup of the ArcticInference Speculator](fig0.png)
*Figure 1 - Speedup of Llama-3.1-70B-Instruct by the ArcticInference Speculator on a 8xH100 GPU node. Illustration courtesy of Snowflake, Inc.*

A significant breakthrough driving these performance enhancements is **SuffixDecoding**, a model-free speculation technique rooted in suffix trees. I led the SuffixDecoding project during my research internship at Snowflake, and I will provide a comprehensive overview below.

## Introduction

The exponential rise in the adoption and integration of large language models (LLMs) into production-grade machine learning systems has catalyzed a transformation in AI-powered applications spanning diverse domains—ranging from open-domain dialogue agents to code synthesis platforms and structured database querying via natural language. Yet, a critical bottleneck persists: high inference latency. This latency substantially hampers the scalability and responsiveness of these applications, especially in latency-sensitive or throughput-constrained deployments.

This article introduces **SuffixDecoding**, a novel, principled, and deployable framework for accelerating LLM inference by leveraging speculative decoding without relying on auxiliary draft models, specialized decoding heads, or any model training. Developed through a research collaboration between Carnegie Mellon University and Snowflake AI Research, SuffixDecoding innovatively employs **suffix trees**—compact data structures constructed from historical LLM outputs—to generate candidate token sequences for speculative verification. The design minimizes GPU memory overhead and avoids the orchestration complexity that accompanies multi-model serving pipelines. Instead, it harnesses the vast and underutilized CPU memory available in modern inference systems to achieve throughput gains and improved latency.

<!-- Figure Placeholder: Overview diagram of SuffixDecoding (Figure 1 from paper) -->
<!-- ![Overview diagram of SuffixDecoding](fig1.png) -->


## Background: Speculative Decoding

Autoregressive decoding in LLMs entails two primary computational phases: (1) a **prefill stage**, wherein the model processes the input context (prompt tokens), and (2) a **decoding stage**, which generates the output tokens sequentially. While the prefill stage can be executed in parallel across tokens, the decoding phase is intrinsically **sequential**, as each new token depends on the full context formed by prior tokens. This sequentiality inhibits parallelism and incurs significant latency for long generations—an issue magnified in multi-agent systems or tasks requiring extensive output generation.

Speculative decoding has emerged as a promising class of techniques to reduce latency. It involves generating multiple candidate tokens using a lightweight approximation (e.g., a draft model), and then verifying them in a single forward pass using the full model. This speculative mechanism reduces the number of forward passes required per generated token. However, model-based speculative decoding introduces several engineering and systems challenges:

- It necessitates the co-deployment of a secondary draft model, complicating orchestration and introducing tight coupling between model pairs.
- It increases memory pressure on GPU resources, limiting the room available for KV cache and attention state.
- It often requires model-specific fine-tuning to align the outputs of the draft model and the full model.

**SuffixDecoding** circumvents these limitations entirely by eliminating the need for any auxiliary model. Instead, it sources speculative candidates from previously observed sequences encoded in suffix trees—enabling speculative decoding with **no additional model inference**.

## Motivation: Agentic Workflows

Modern **agentic workflows** frequently involve iterative self-reflection loops and multiple reasoning paths, producing outputs with **highly predictable and repetitive patterns**. However, traditional speculative decoding methods typically only predict a few tokens at a time, failing to fully leverage these repetitive structures for acceleration. 

SuffixDecoding addresses this gap by providing a **lightweight speculative approach** that exploits repetitive textual patterns through dynamically constructed sequences based on both historical outputs and current inputs. Rather than using a fixed speculation length, SuffixDecoding **adaptively identifies** matching sequences with high probability of occurrence.

The core innovation lies in maintaining a compact cache of previously generated sequences using **suffix trees**—an efficient data structure for indexing and matching repeating token patterns from both historical generations and the current prompt. This optimized structure enables SuffixDecoding to speculate tokens with **remarkable speed** (approximately 20 microseconds per token), facilitating adaptive speculation of **significantly longer sequences** than conventional methods allow.

## How SuffixDecoding Works

### Step 1: Building Suffix Trees

At the core of SuffixDecoding is the insight that many real-world LLM deployments exhibit **highly structured and repetitive outputs**, especially in domains such as structured code generation, conversational templates, and text-to-SQL transformations. To exploit these regularities, SuffixDecoding maintains suffix trees constructed from prior prompt-response pairs.

The system employs two distinct suffix tree structures:
- A **global suffix tree**, which is constructed offline (or incrementally online) from the outputs of historical inference traces.
- A **per-request suffix tree**, which is constructed at runtime using the current prompt and partial generation tokens.

Each suffix tree represents token sequences as tree paths: each node corresponds to a token, and a path from the root to a node denotes a suffix of some previous output. These trees are stored in CPU memory, enabling high-capacity pattern storage without taxing GPU resources.

<!-- Figure Placeholder: Example suffix tree and pattern matching -->

### Step 2: Pattern Matching and Candidate Selection

At each decoding step, SuffixDecoding extracts a **pattern sequence**: a suffix of the most recent output tokens (e.g., the last \( p \) tokens). This sequence is used to traverse the suffix tree. If a match is found, the subtree rooted at the match node yields possible continuations—i.e., candidate token sequences observed in similar contexts.

SuffixDecoding employs a **greedy expansion algorithm** to construct a **speculation tree** from this subtree. It prioritizes continuations that have high empirical probability, based on token frequencies recorded in the suffix tree. This allows the system to generate plausible candidate tokens for verification.

### Step 3: Tree-Based Verification

The constructed speculation tree is then passed to the LLM, which verifies the candidate tokens in a single forward pass using a topology-aware causal attention mask. Tokens that align with the model's actual outputs are accepted and appended to the generated sequence. Unverified tokens are discarded, and decoding resumes from the point of acceptance.

Through this process, multiple tokens are potentially appended per decoding step, reducing the number of forward passes needed and accelerating inference.

<!-- Figure Placeholder: Speculation tree with verified tokens highlighted -->

## Adaptive Tree Expansion: Greedy but Informed

A notable feature of SuffixDecoding is its adaptive control over speculation granularity. The algorithm defines a speculation bound \\( \text{MAX_SPEC} = \alpha p \\), where \\( p \\) is the matched pattern length and \\( \alpha \\) is a tunable parameter. Intuitively, longer matched suffixes provide stronger predictive grounding, enabling deeper speculation trees.

### Scoring Function for Candidate Subtrees

To prioritize speculation trees likely to yield high token acceptance, SuffixDecoding uses a scoring function:

\\[
\text{SCORE}(T_{\text{spec}}) = \sum_{N \in T_{\text{spec}}} D(N)
\\]

Here, \\( D(N) \\) represents the estimated empirical probability of the token at node \\( N \\) being accepted, computed from observed frequencies in the reference corpus. The speculation tree with the highest score is selected for verification.

## Implementation Details

The SuffixDecoding system is implemented in high-performance C++ on top of **FlexFlow Serve**, a distributed LLM serving framework optimized for GPU inference. The system integrates tightly with CUDA-based kernels for attention computations and uses NCCL for inter-GPU communication.

Crucially, suffix tree operations and speculation logic run on CPU resources. This design leverages the abundant main memory and compute capacity typically available on inference nodes (e.g., AWS p5.48xlarge nodes feature 2TB of RAM and hundreds of CPU cores), enabling scalable speculative decoding without GPU interference.

<!-- Figure Placeholder: System architecture block diagram -->

## Evaluation

We evaluated SuffixDecoding across four representative tasks, spanning diverse LLM application domains:

1. **WildChat**: User-assistant conversations with unstructured open-domain prompts.
2. **Magicoder**: Instruction-tuned prompts for code generation.
3. **SpiderSQL**: Complex natural language to SQL conversion over diverse schemas.
4. **AgenticSQL**: A multi-stage LLM pipeline for structured database query generation in a proprietary production system.

Baseline comparisons include:
- **Incremental decoding**: canonical token-by-token autoregressive generation.
- **SpecInfer**: a draft-model-based speculative decoding method employing tree-based verification.

### Results Overview

SuffixDecoding demonstrates consistent performance improvements across all settings:

- On AgenticSQL, it achieves **up to 3× lower time-per-token latency** and **2.9× higher throughput** than SpecInfer.
- On open-ended chat and coding tasks, it offers **1.4× higher throughput** than model-based speculative decoding.
- Acceptance rates remain stable across tasks and comparable to baseline methods, with **zero additional GPU cost**.

<!-- Figure Placeholder: Throughput bar chart (Figure 4) -->
<!-- Figure Placeholder: TPOT latency bar chart (Figure 5) -->

## Ablation Studies and Insights

### Global vs Per-Request Suffix Trees

We performed a detailed ablation to quantify the contribution of global and per-request suffix trees. The hybrid configuration—using both trees—consistently outperformed either component alone. Per-request trees were particularly effective in tasks where prompt re-use is prevalent, such as the Combine stage of AgenticSQL. Global trees generalized better across heterogeneous tasks.

<!-- Figure Placeholder: Ablation speedup comparison (Figure 7) -->

### Suffix Tree Size and Performance Scaling

We evaluated SuffixDecoding with global suffix trees ranging from **256 to 10,000 examples**. Results show:

- With only 256 examples, speedups of **1.36× to 1.45×** are observed.
- With 10,000 examples, speedups exceed **1.7×**, demonstrating robust scaling.

Acceptance rates remain largely unaffected by corpus size, suggesting that speculation quality degrades gracefully even with limited reference data.

<!-- Figure Placeholder: Speedup vs. tree size plot (Figure 8) -->

### Online Adaptation to Input Distribution Shifts

To test adaptability, we evaluated SuffixDecoding trained on WildChat outputs and deployed on SpiderSQL queries—representing a substantial distributional shift. Despite the mismatch, SuffixDecoding retained **1.5× speedup** and adapted rapidly. After ingesting 500 SpiderSQL responses into the suffix tree, it matched the performance of a model trained offline on SpiderSQL.

<!-- Figure Placeholder: Online adaptation performance (Figure 9) -->

## Why It Matters

SuffixDecoding represents a departure from conventional wisdom that speculative decoding requires auxiliary models. By **indexing previously generated outputs**, it delivers inference acceleration without additional GPU usage, model training, or orchestration complexity.

This makes it especially appealing for:
- Cost-efficient, low-latency LLM deployments.
- Multi-agent pipelines with highly structured stages.
- Adaptive inference workloads with shifting input distributions.

## Future Research Directions

SuffixDecoding opens several avenues for continued innovation:
- Integrating learned scoring models or semantic similarity metrics into tree scoring.
- Investigating lossy compression of suffix trees for ultra-large corpora.
- Developing hybrid speculative decoding methods that fuse model-free and model-based approaches.
- Extending suffix-based speculation to multilingual and multimodal LLMs.

## Conclusion

In summary, SuffixDecoding demonstrates that **model-free speculative decoding is not only possible but competitive** with state-of-the-art draft-model-based methods. By reusing historical outputs through efficient suffix tree indexing and adaptive candidate scoring, it delivers significant improvements in latency and throughput across a wide range of LLM tasks.

Its simplicity, scalability, and deployment friendliness position it as a compelling direction for future LLM inference systems.

<!-- Figure Placeholder: SuffixDecoding summary graphic -->

Stay tuned as we continue to investigate how to push the boundaries of efficient LLM serving systems—without sacrificing quality or generality.

<!-- # Section Heading

## Subsection Heading

Some text.

## Another Subsection Heading

Some more text.
You can write lines
separately
and it'll still
be considered
a single paragraph. Paragraphs are separated by a
blank line.

# Another Section

You can **bold** things by wrapping them in two asterisks/stars. You
can _italicise_ things by wrapping them in underscores. You can also
include inline `code` which is done by wrapping with backticks (the
key likely to the left of the 1 on your keyboard).

If you want to add larger snippets of code, you can add triple
backticks around them, like so:

```
this_is_larger = true;
show_code(true);
```

However, the above doesn't add syntax highlighting. If you want to do
that, you need to specify the specific language on the first line, as
part of the backticks, like so:

```c
#include <stdio.h>

int main() {
   printf("Hello World!");
   return 0;
}
```

If you want to quote someone, simply prefix whatever they said with a
`>`. For example:

> If it is on the internet, it must be true.

-- Abraham Lincoln

You can also nest quotes:

> > You miss 100% of the shots you don't take
>
> -- Wayne Gretzky

-- Michael Scott

Every paragraph _immediately_ after a quote is automatically right
aligned and pressed up against the quote, since it is assumed to be
the author/speaker of the quote. You can suppress this by adding a
`<p></p>` right after a quote, like so:

> This is a quote, whose next para is a normal para, rather than an
> author/speaker

<p></p>

This paragraph is perfectly normal, rather than being forced
right. Additionally, you could also add a `<br />` right beside the
`<p></p>` to give some more breathing room between the quote and the
paragraph.

In the author notifications above, btw, note how the double-hyphen
`--` automatically becomes the en-dash (--) and the triple-hyphen
`---` automatically becomes the em-dash (---). Similarly, double- and
single-quotes are automagically made into "smart quotes", and the
ellipsis `...` is automatically cleaned up into an actual ellipsis...

---

You can add arbitrary horizontal rules by simply placing three hyphens
on a line by themselves.

---

Of course, you can write \\( \LaTeX \\) either inline by placing stuff
within `\\(` and `\\)` markers, or as a separate equation-style LaTeX
output by wrapping things in `\\[` and `\\]`:

\\[ \sum_{n_1 \in \N} \frac{n_1}{n_2} \\]

Alternatively, you can wrap it inside of a pair of double-dollar signs
`$$`:

$$ \frac{\Phi \in \psi}{\psi \rightarrow \xi} $$

Single dollar signs unfortunately do not work for inline LaTeX.

# More fun!

Of course, you can add links to things, by using the right syntax. For
example, [here is a link to NASA](https://www.nasa.gov/). Standard
HTML-like shenanigans, such as appending a `#anchor` to the end of the
link also work. Relative links within the website also work.

You can also use the links to link back to parts of the same
blogpost. For this, you need to find the "slug" of the section. For
this, you can force a slug at the section heading, and then simply
refer to it, like the [upcoming section](#finale), or alternatively,
you can take the lowercase version of all the parts of a section and
place hyphens between them, like [this](#more-fun) or
[this](#another-section).

Pictures, of course, can be added. The best way to do this is to
utilize relative links (just add images into the right directory, see
the main `README` file in this repository to learn where it should
go), but you can link to external images too in the same way. For
example,

![i are serious cat](https://upload.wikimedia.org/wikipedia/commons/4/44/CatLolCatExample.jpg)

Of course, it is good etiquette to add alt-text to your images, like
has been done in the previous image, with "i are serious cat". It
helps with accessibility.

Images are automatically shown at a reasonable size by limiting their
maximum width. If you have a particularly tall image, you might have
to do some manipulation yourself though. Images should also
automatically work properly in mobile phones :)

---

Do you want some tables? Here are some tables:


| Header 1   | Another header here   | This is a long header |
|:---------- | ---------------------:|:---------------------:|
| Some data  | Some more data        | data \\( \epsilon \\) |
| data       | Some _long_ data here | more data             |
| align left |   right               | center                |

You use the `:` specifier in the table header-body splitting line to
specify whether the particular column should be left, center, or right
aligned. All the standard markdown elements continue to work within
the table, so feel free to use them.

# Finale {#finale}

Finally, you're at the end of your blogpost! Your name will appear
again at the end automatically, as will the committee members who will
(hopefully) approve your blogpost with no changes! Good luck! -->
