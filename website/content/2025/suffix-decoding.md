+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "SuffixDecoding: Model-Free Acceleration for LLM Inference"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2025-05-03

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

Snowflake recently unveiled [ArcticInference](https://www.snowflake.com/en/engineering-blog/fast-speculative-decoding-vllm-arctic/), the fastest speculative decoding solution for vLLM currently available. ArcticInference can reduce the end-to-end latency for **LLM agent tasks** by up to **4 times** and can improve **open-ended chat completion** workloads by as much as **2.8 times**. A key breakthrough contributing to these performance enhancements is [SuffixDecoding](https://arxiv.org/abs/2411.04975), a model-free speculation technique based on suffix trees, which I developed during my research internship at Snowflake.

![Speedup of the ArcticInference Speculator](fig0.webp)
*Figure 1 - Speedup of Llama-3.1-70B-Instruct by the ArcticInference Speculator on a 8xH100 GPU node. Illustration courtesy of Snowflake, Inc.*

In this blog post, I will first provide an overview of LLM inference and speculative decoding. Then, I will introduce SuffixDecoding and guide the reader through its use cases, design, and evaluation.

## Introduction

The exponential growth of **large language models (LLMs)** in production systems has transformed applications across domains—from dialogue agents to code synthesis and natural language database querying. However, a critical bottleneck remains: **high inference latency**, which hampers responsiveness in latency-sensitive applications.

**Speculative decoding** has emerged as a promising solution, generating multiple candidate tokens using lightweight approximations (e.g., draft models) and verifying them in a single forward pass. While effective for open-ended chat, traditional speculative approaches fall short in two key areas:

1. **Contextually grounded generation** (such as SQL generation with schema information or RAG-based responses), where significant overlap exists between responses and grounding context.

2. **Agentic tasks**, where LLMs interact with external tools (such as bash, python, etc) across multiple generation steps, creating substantial token repetition between subsequent responses.

Conventional speculative methods cannot leverage these repeated token patterns. While fine-tuning draft models is possible, it introduces significant challenges: time costs, operational complexity, and limited model capacity to adapt to user-specific contexts. Additionally, model-based approaches create substantial engineering and resource allocation challenges in production environments.

### Can we accelerate contextually grounded generation and agentic tasks beyond what is currently supported by speculative decoding?

Motivated by this challenge, our team at Snowflake AI Research and Carnegie Mellon University developed **SuffixDecoding** - a breakthrough approach that accelerates LLM inference without any auxiliary models. Unlike traditional methods, SuffixDecoding doesn't require draft models, specialized decoding heads, or model training of any kind. Instead, it cleverly employs **suffix trees** - elegant data structures built from previous LLM outputs - to generate speculative token sequences for verification.

What makes SuffixDecoding particularly powerful is its resource efficiency. By shifting the speculative workload to CPU memory (which often sits largely unused on modern inference servers), it minimizes GPU overhead while avoiding the complexity of orchestrating multi-model pipelines. The result? Significantly improved throughput and reduced latency across diverse LLM applications, all with minimal implementation overhead.

## Background: Autoregressive LLM Inference and Speculative Decoding

Autoregressive decoding in LLMs entails two primary computational phases: (1) a **prefill stage**, wherein the model processes the input context (prompt tokens), and (2) a **decoding stage**, which generates the output tokens sequentially. While the prefill stage can be executed in parallel across tokens, the decoding phase is intrinsically **sequential**, as each new token depends on the full context formed by prior tokens. This sequentiality inhibits parallelism and incurs significant latency for long generations—an issue magnified in multi-agent systems or tasks requiring extensive output generation.

![Speculative decoding timeline compared to incremental decoding](spec-decoding-timeline.png)
*Figure 2 - The Speculative Decoding timeline compared to Incremental Decoding. At each step, the draft model is first called to generate a sequence (or a tree) of candidate tokens. Then, the tokens are passed to the LLM for verification in a single forward pass.*

Speculative decoding addresses this limitation by using a draft model to generat multiple candidate tokens at once at a small fraction of the cost that it would take for the LLM to generate them. Then, it uses the LLM to verify them in parallel in a single forward pass. Several techniques have been developed in this space. The **EAGLE** family of speculators trains a small model that directly predicts future tokens using features from multiple layers of the main model, improving both accuracy and scalability. **Medusa** adds lightweight parallel heads to the main model itself, allowing it to predict several next tokens in one step without needing a separate draft model. **SpecInfer** builds a tree of possible continuations using a small helper model and verifies the entire tree in parallel, increasing the number of accepted tokens per step. **REST** skips modeling altogether by retrieving likely next tokens from a datastore of past examples, making it easy to use with any language model without additional training. 

Model-based suffix decoding works reasonably well for open-ended chat, but has the following limitations:
- It necessitates the co-deployment of a secondary draft model, complicating orchestration and introducing tight coupling between model pairs.
- It increases memory pressure on GPU resources, limiting the room available for KV cache and attention state.
- It often requires model-specific fine-tuning to align the outputs of the draft model and the full model.

### Background: Model-free speculative decoding
Model-free speculative decoding solutions avoid the overhead of maintaining auxiliary draft models by leveraging alternative techniques to generate speculative tokens. Notable approaches include **prompt lookup decoding**, which sources candidate tokens from the prompt. **Lookahead Decoding** generates draft tokens using a Jacobi iteration method. **REST** retrieves draft tokens from a library of external texts. **Token Recycling** builds a cache of possible continuations based on the top-k tokens that are not picked at decoding time. The key insight unifying these methods is that statistical regularities in language can enable effective speculation without the computational burden of additional neural models. However, these methods often lack the adaptability and efficiency of SuffixDecoding, which dynamically leverages historical outputs to exploit repetitive patterns in real-time.


## Motivation: Why Suffix Decoding?

**SuffixDecoding** circumvents these limitations entirely by eliminating the need for any auxiliary model. Instead, it sources speculative candidates from previously observed sequences encoded in suffix trees—enabling speculative decoding with **no additional model inference**.

Modern **agentic workflows** frequently involve iterative self-reflection loops and multiple reasoning paths, producing outputs with **highly predictable and repetitive patterns**. However, traditional speculative decoding methods typically only predict a few tokens at a time, failing to fully leverage these repetitive structures for acceleration. 

SuffixDecoding addresses this gap by providing a **lightweight speculative approach** that exploits repetitive textual patterns through dynamically constructed sequences based on both historical outputs and current inputs. Rather than using a fixed speculation length, SuffixDecoding **adaptively identifies** matching sequences with high probability of occurrence.

The core innovation lies in maintaining a compact cache of previously generated sequences using **suffix trees**—an efficient data structure for indexing and matching repeating token patterns from both historical generations and the current prompt. This optimized structure enables SuffixDecoding to speculate tokens with **remarkable speed** (approximately 20 microseconds per token), facilitating adaptive speculation of **significantly longer sequences** than conventional methods allow.

### Agentic Workflow: Solving SWE-Bench tasks with CodeAct

![The SWE-Bench benchmark workflow](swebench-diagram.png)
*Figure 3 - The SWE-Bench benchmark workflow. Illustration courtesy of SWE-Bench.*

Many off-the-shelves LLMs today have the ability to generate code, but this ability is often limited to solving self-contained tasks, or assisting the user while editing a single source file. To solve more **complex programming tasks**, many teams have been prototyping AI agents that use an LLM in conjunctions with external tools to interact with the environment. Solving a single software engineering task can however take the agent **several minutes** or longer, and this can cause a barrier to user interaction and adoption. SuffixDecoding can help to significantly cut back the end-to-end latency of coding tasks, up to 4.5x in our experiments.

To evaluate the effectiveness of SuffixDecoding, we run the [CodeAct 2.1](https://www.all-hands.dev/blog/openhands-codeact-21-an-open-state-of-the-art-software-development-agent) agent with the `all-hands/openhands-lm-32b-v0.1-ep3` LLM on the full [SWE-Bench Verified](https://openai.com/index/introducing-swe-bench-verified/) dataset. CodeAct 2.1 is an open-source software development agent designed by OpenHands to solve **realistic programming tasks** (such as Github issues) by executing Python code as its primary form of action. Unlike agents that rely on structured text or JSON formats, CodeAct embraces executable code to unify the agent’s action space, enabling rich control flow, tool composition, and self-debugging. CodeAct is compatible with closed-source LLMs accessible via API (such as GPT-4o, o3, or Claude Sonnet), as well as open-source models served locally with an inference framework such as vLLM. 

We chose CodeAct as it is one of the best-performing open-source agents on the **SWE-bench Verified** leaderboard. SWE-bench is a popular and challenging benchmark designed to evaluate the capabilities of language models in realistic software engineering tasks. Unlike traditional code generation tasks, SWE-bench demands cross-file reasoning, long-context understanding, and complex patch generation. SWE-bench Verified is a subset of the SWE-bench suite curated by OpenAI. Each instance of SWE-Bench Verified has been carefully vetted by a team of software developers to ensure that is indeed solvable. Each task in the Verified subset is paired with one or more “fail-to-pass” tests, ensuring that successful patches do not just compile, but also resolve the core issue behaviorally. 

![End-to-end speedup of CodeAct on the SWE-Bench Verified benchmark](swebench-perf.webp)
*Figure 4 - End-to-end speedup of CodeAct on the SWE-Bench Verified benchmark. Illustration courtesy of Snowflake, Inc.*


### Contextually-grounded generation: Writing SQL for Cortex-Analyst

![The Cortex Analyst multi-stage LLM pipeline](cortex-analyst.png)
*Figure 5 - Cortex Analyst's multi-stage LLM pipeline workflow. Illustration courtesy of Snowflake, Inc.*

[Cortex Analyst](https://www.snowflake.com/en/blog/cortex-analyst-ai-self-service-analytics/) employs a multi-stage LLM pipeline to translate natural language questions into executable SQL code. This pipeline includes several specialized stages: query intent understanding, metadata retrieval, disambiguation, and final code generation. At each step, the LLM is guided by structured context—such as the user’s database schema, column names, data types, and business-specific semantic models—to incrementally refine the query.

Contextually-grounded generation is critical in this pipeline because the final SQL code is not shown to the user for manual review; instead, it is executed directly to return results. Unlike traditional code assistants where placeholders or vague constructs might be acceptable, Cortex Analyst must produce executable, schema-valid code on the first attempt. Any hallucination or misinterpretation—such as referencing a non-existent table or misunderstanding column semantics—would cause execution failures or incorrect results. Thus, precise grounding in the live database context ensures both reliability and safety of the automated analytics process.

SuffixDecoding can significantly accelerate Cortex Analyst's SQL generation pipeline through several mechanisms:

1. **Context-aware acceleration**: By storing previous SQL generations in suffix trees, SuffixDecoding can speculate tokens based on similar database schema patterns and query structures that appeared in prior analysis sessions.

2. **Schema-specific optimizations**: When users query the same database repeatedly, the suffix tree captures common table joins, column references, and aggregation patterns specific to their schema, enabling more accurate speculation for new but structurally similar queries.

3. **Multi-stage pipeline efficiency**: Cortex Analyst's staged approach creates significant token overlap between steps. SuffixDecoding leverages this by using the output from earlier stages (intent understanding, disambiguation) to predict subsequent stages (SQL generation).

4. **Adaptive to user patterns**: As users develop characteristic query patterns against their database, SuffixDecoding's per-request suffix tree captures these patterns, enabling more personalized and accurate speculation for individual analysts.

Our experiments with Cortex Analyst showed that SuffixDecoding reduced end-to-end latency by up to 2.8× compared to standard autoregressive decoding, with minimal implementation overhead. Particularly in multi-stage pipelines where subsequent stages build upon earlier outputs, acceptance rates reached as high as 70-80%, effectively amortizing the cost of LLM inference across multiple tokens.

## Design: How does Suffix Decoding work?

![Overview diagram of SuffixDecoding](fig1.png)
Fig 6 - Overview diagram of SuffixDecoding

### Step 1: Building Suffix Trees

At the core of SuffixDecoding is the insight that many real-world LLM deployments exhibit **highly structured and repetitive outputs**, especially in domains such as structured code generation, conversational templates, and text-to-SQL transformations. To exploit these regularities, SuffixDecoding maintains suffix trees constructed from prior prompt-response pairs.

The system employs two distinct suffix tree structures:
- A **global suffix tree**, which is constructed offline (or incrementally online) from the outputs of historical inference traces.
- A **per-request suffix tree**, which is constructed at runtime using the current prompt and partial generation tokens.

Each suffix tree represents token sequences as tree paths: each node corresponds to a token, and a path from the root to a node denotes a suffix of some previous output. These trees are stored in CPU memory, enabling high-capacity pattern storage without taxing GPU resources.

### Step 2: Pattern Matching and Candidate Selection

At each decoding step, SuffixDecoding extracts a **pattern sequence**: a suffix of the most recent output tokens (e.g., the last \( p \) tokens). This sequence is used to traverse the suffix tree. If a match is found, the subtree rooted at the match node yields possible continuations—i.e., candidate token sequences observed in similar contexts.

SuffixDecoding employs a **greedy expansion algorithm** to construct a **speculation tree** from this subtree. It prioritizes continuations that have high empirical probability, based on token frequencies recorded in the suffix tree. This allows the system to generate plausible candidate tokens for verification.

### Step 3: Tree-Based Verification

![Overview diagram of SuffixDecoding](tree-based-verification.png)
Fig 7 - Overview diagram of Tree-Based Verification in a single forward pass

The constructed speculation tree is then passed to the LLM, which verifies the candidate tokens in a single forward pass using a topology-aware causal attention mask. Tokens that align with the model's actual outputs are accepted and appended to the generated sequence. Unverified tokens are discarded, and decoding resumes from the point of acceptance.

Through this process, multiple tokens are potentially appended per decoding step, reducing the number of forward passes needed and accelerating inference.

## Adaptive Tree Expansion: Greedy but Informed

A notable feature of SuffixDecoding is its adaptive control over speculation granularity. The algorithm defines a speculation bound \\( MAX\\_SPEC = \alpha p \\), where \\( p \\) is the matched pattern length and \\( \alpha \\) is a tunable parameter. Intuitively, longer matched suffixes provide stronger predictive grounding, enabling deeper speculation trees.

### Scoring Function for Candidate Subtrees

To prioritize speculation trees likely to yield high token acceptance, SuffixDecoding uses a scoring function:

\\[
\text{SCORE}(T_{\text{spec}}) = \sum_{N \in T_{\text{spec}}} D(N)
\\]

Here, \\( D(N) \\) represents the estimated empirical probability of the token at node \\( N \\) being accepted, computed from observed frequencies in the reference corpus. The speculation tree with the highest score is selected for verification.

## Implementation Details

The SuffixDecoding system is implemented in high-performance C++ on top of **FlexFlow Serve**, a distributed LLM serving framework optimized for GPU inference. The system integrates tightly with CUDA-based kernels for attention computations and uses NCCL for inter-GPU communication. We also offer a vLLM implementation with a subset of features. 

Crucially, suffix tree operations and speculation logic run on CPU resources. This design leverages the abundant main memory and compute capacity typically available on inference nodes (e.g., AWS p5.48xlarge nodes feature 2TB of RAM and hundreds of CPU cores), enabling scalable speculative decoding without GPU interference.

## Evaluation

We evaluated SuffixDecoding across four representative tasks, spanning diverse LLM application domains:

1. **WildChat**: User-assistant conversations with unstructured open-domain prompts.
2. **Magicoder**: Instruction-tuned prompts for code generation.
3. **SpiderSQL**: Complex natural language to SQL conversion over diverse schemas.
4. **AgenticSQL**: A multi-stage LLM pipeline for structured database query generation based on an early prototype of Cortex-Analyst.

Baseline comparisons include:
- **Incremental decoding**: canonical token-by-token autoregressive generation.
- **SpecInfer**: a draft-model-based speculative decoding method employing tree-based verification.

### Results Overview

SuffixDecoding consistently improves performance across diverse tasks:

- On AgenticSQL, a multi-stage text-to-SQL application, it achieves **up to 2× higher throughput** and **2.2× lower time-per-token (TPOT) latency** compared to SpecInfer.
- On open-ended chat (WildChat) and code generation (Magicoder) tasks, it attains up to **1.2× higher throughput** than SpecInfer, with competitive performance despite using only a small fraction of the data required to train a draft model.
- Acceptance rates remain robust across tasks, and SuffixDecoding introduces **no additional GPU cost**, leveraging CPU memory and tree-based pattern matching for candidate generation.

![Throughput and TPOT of SuffixDecoding](throughput-tpot.png)
Figure 8: SuffixDecoding compared to baselines. TOP: generation throughput. BOTTOM: Per-request TPOT.

![Speculation stats](table-results.png)
Table 1: Speculation stats for different decoding methods. SD-T: SuffixDecoding with tree speculation; SD-L: SuffixDecoding with linear speculation; SPEC-1B and SPEC-8B: Tree-Based decoding with SpecInfer using, respectively, LLAMA-3.2-1B and LLAMA-3.1-8B.

## Ablation Studies and Insights

### Global vs Per-Request Suffix Trees

We performed a detailed ablation to quantify the contribution of global and per-request suffix trees. The hybrid configuration—using both trees—consistently outperformed either component alone. Per-request trees were particularly effective in tasks where prompt re-use is prevalent, such as the Combine stage of AgenticSQL. Global trees generalized better across heterogeneous tasks.

<!-- Figure Placeholder: Ablation speedup comparison (Figure 7) -->
![Ablation Speedup](ablation-speedup.png)
*Figure 9 - Speedup factor and number of speculated tokens for the tasks in AgenticSQL. SuffixDecoding was run with only the global suffix tree, only the per-request suffix tree, and both (baseline)*

### Suffix Tree Size and Performance Scaling

We evaluated SuffixDecoding with global suffix trees ranging from **256 to 10,000 examples**. Results show:

- With only 256 examples, speedups of **1.36× to 1.45×** are observed.
- With 10,000 examples, speedups exceed **1.7×**, demonstrating robust scaling.

Acceptance rates remain largely unaffected by corpus size, suggesting that speculation quality degrades gracefully even with limited reference data.

![Speedup vs tree size](speedup-vs-tree-size.png)
*Figure 10 - Speedup (left) and acceptance rate (right) vs global suffix tree size for Magicoder and Wildchat*

### Online Adaptation to Input Distribution Shifts

To test adaptability, we evaluated SuffixDecoding trained on WildChat outputs and deployed on SpiderSQL queries—representing a substantial distributional shift. Despite the mismatch, SuffixDecoding retained **1.5× speedup** and adapted rapidly. After ingesting 500 SpiderSQL responses into the suffix tree, it matched the performance of a model trained offline on SpiderSQL.

![The online adaptation performance of Suffix Decoding](online-adaptation.png)
*Figure 11 - The performance of SuffixDecoding under input distribution shift. SuffixDecoding was trained on outputs from WildChat, while being evaluated on SpiderSQL. X axis: the number of SpiderSQL inputs, which are added to the global suffix tree after they are processed. Red line: the performance of SuffixDecoding if trained on 500 output examples from only SpiderSQL offline*

## Why It Matters

SuffixDecoding represents a departure from conventional wisdom that speculative decoding requires auxiliary models. By **indexing previously generated outputs**, it delivers inference acceleration without additional GPU usage, model training, or orchestration complexity.

This makes it especially appealing for:
- Cost-efficient, low-latency LLM deployments.
- Multi-agent pipelines with highly structured stages.
- Adaptive inference workloads with shifting input distributions.

## Conclusion

In summary, SuffixDecoding demonstrates that **model-free speculative decoding is not only possible but competitive** with state-of-the-art draft-model-based methods. By reusing historical outputs through efficient suffix tree indexing and adaptive candidate scoring, it delivers significant improvements in latency and throughput across a wide range of LLM tasks.

Its simplicity, scalability, and deployment friendliness position it as a compelling direction for future LLM inference systems.

Stay tuned as we continue to investigate how to push the boundaries of efficient LLM serving systems—without sacrificing quality or generality.


## References
- Cai, T. et al. (2024). Medusa: Simple LLM Inference Acceleration Framework with Multiple Decoding Heads.
- Chowdhury, N. et al. (2024). Introducing SWE-bench Verified.
- Forero, J. et al. (2024). Cortex Analyst: Paving the Way to Self-Service Analytics with AI.
- Fu, Y. et al. (2024). Break the Sequential Dependency of LLM Inference Using Lookahead Decoding.
- Jimenez, C. et al. (2023). SWE-bench: Can Language Models Resolve Real-World GitHub Issues?
- Li, Y. et al. (2024). EAGLE-2: Faster Inference of Language Models with Dynamic Draft Trees.
- Li, Y. et al. (2025). EAGLE-3: Scaling up Inference Acceleration of Large Language Models via Training-Time Test.
- Luo, X. et al. (2024). Turning Trash into Treasure: Accelerating Inference of Large Language Models with Token Recycling.
- Miao, X. et al. (2024). SpecInfer: Accelerating Generative Large Language Model Serving with Tree-based Speculative Inference and Verification.
- Oliaro, G. et al. (2024). SuffixDecoding: A Model-Free Approach to Speeding Up Large Language Model Inference.
- Saxena, A. (2024). Prompt Lookup Decoding.
- Sun, Z. et al. (2023). SpecTr: Fast Speculative Decoding via Optimal Transport.
- Wang, X. et al. (2024). Executable Code Actions Elicit Better LLM Agents.
- Wang, Y. et al. (2025). Fastest Speculative Decoding in vLLM with Arctic Inference and Arctic Training.
- Zhao, Y. et al. (2024). Lookahead: An Inference Acceleration Framework for Large Language Model with Lossless Generation Accuracy.
