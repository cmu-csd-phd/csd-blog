+++
title = "Closing the Transformer-SSM Gap with Retrieval-Aware Distillation"
date = 2026-10-09

[taxonomies]
areas = ["Artificial Intelligence"]
tags = ["large language models", "long-context", "attention", "ssms", "hybrid models", "knowledge distillation"]

[extra]
author = {name = "Aviv Bick", url = "https://avivbick.github.io" }
committee = [
    {name = "Graham Neubig", url = "https://www.phontron.com/"},
    {name = "Tim Dettmers", url = "https://timdettmers.com/"},
    {name = "Yonghao Zhuang", url = "https://zyhowell.github.io"}
]
+++

Long-context understanding is a critical frontier for large language models (LLMs). Many of the most valuable applications, such as code generation, processing entire books, and modeling DNA sequences, either require long-context understanding to work well or become dramatically more capable when given them. The core obstacle, however, is memory: the attention mechanism in Transformers caches the entire past sequence, so both memory and the bandwidth needed to access it grow linearly with sequence length, making long contexts expensive at training and inference time alike.

State space models (SSMs) sidestep this by compressing the past into a fixed recurrent state, giving them a constant memory footprint regardless of sequence length. But compression comes at a cost.
Loading an entire book into context is only useful if the model can actually retrieve what it read: recalling, for instance, the name of a character briefly introduced hundreds of pages earlier when a user asks about them. This capability, known as *in-context retrieval*, is where SSMs struggle: by forcing history into a fixed-size vector, they lose the explicit addressable memory that makes Transformers so effective at it [\[1,2\]](#references).

Hybrid models that interleave attention and SSM layers, often in a 1:3 ratio [\[3,4\]](#references), have been proposed as a way to get the best of both worlds, and have shown impressive performance on retrieval-heavy tasks. However, even at 25% attention heads, the memory cost remains substantial. Attempts to push further by preserving even fewer attention layers have met with limited success, leaving the field stuck far from the memory efficiency that pure SSMs promise.

Yet as we show, just 2% of attention heads are enough for a hybrid to perform well. To see why so few heads suffice, we first need to understand how current hybrids achieve their retrieval performance in the first place, and why current methods fail.

# Gather-and-Aggregate as a Bottleneck
In prior work [\[2\]](#references), we showed that in-context retrieval in LLMs is carried out by a handful of specialized heads, termed Gather-and-Aggregate (G&A) heads, while the rest of the network focuses on local processing. This holds across architectures, whether pure Transformer, pure SSM, or hybrid.

The experiment showing this is rather simple: we go through each head in a trained model, zero-out its parameters, and query the model on a retrieval task. Consider the following example, where the model is shown a list of key-value pairs and asked to retrieve a specific value:

>Memorize the following dictionary: <br> present:50<br> institute:0<br> scallops:84<br> neuropsychiatry:67<br> The value of the key 'scallops' is: ___

<p></p>

We find that most heads can be knocked out with little to no effect --- the model still returns the correct answer ("84"). But a small number of heads are critical: removing them causes the model to return a wrong value, revealing that retrieval depends almost entirely on these few heads.

G&A heads reframe the Transformer-SSM gap more precisely: SSMs do not simply lack memory, they struggle to faithfully execute these specific retrieval heads given their compressed state. In hybrids, however, the model learns to delegate this responsibility to the attention heads, which are better suited for it, while SSM layers handle everything else.

Yet current hybrids still preserve far more attention heads than this picture seems to require. If retrieval is concentrated in just a few heads, then perhaps hybrids can preserve even fewer. But since these heads are scattered non-uniformly throughout the network, the old approach of picking a fixed attention-to-SSM ratio will not find them.

# Becoming Retrieval-Aware
Once we understand the problem in the previous section, the solution is pretty straightforward: we want to keep attention heads only where they are actually needed for retrieval, and have the SSM handle the rest. Since one cannot predict in advance which heads those are (at least not at the time of writing this post), we instead identify them in an already-trained Transformer and use it as a teacher, distilling it into a leaner hybrid student whose attention placement is guided by retrieval function rather than a fixed ratio. We call this **Retrieval-Aware Distillation**, and it works in three steps.

**1. Score the heads:** Using the same knockout experiment from the previous section, we measure the retrieval importance of each head in the trained Transformer teacher. Heads whose removal damages retrieval the most are deemed important. This gives a highly *non-uniform map* where some heads matter a lot, and many heads matter very little.

**2. Threshold and replace:** Once every head has a retrieval-importance score, preserve only those above a threshold as attention heads in the student. Everything else gets replaced by recurrent SSM-style heads. The resulting architecture is a Transformer-SSM hybrid, but not one designed by a simple ratio --- its structure is determined by retrieval function.

**3. Distill:** Finally, distill the teacher into the hybrid student. The student is initialized with the preserved attention heads and learns to recover the teacher's behavior.

## How Many Attention Heads Need to Be Preserved?

We now show the results of applying Retrieval-Aware Distillation to Llama-1B and Qwen2-1.5B, two of the most widely used models in that scale. We vary the number of preserved attention heads and evaluate the resulting hybrids on two groups of tasks: retrieval-heavy tasks, which require in-context retrieval to perform well, and knowledge-focused tasks, which rely more on the model's internal knowledge and local processing. This allows us to see how the number of preserved attention heads affects retrieval performance specifically, ruling out the possibility that these heads are doing something else.

<figure style="text-align:left; margin:1.25rem 0;">
  <img src="./retrieval-performance.png" alt="Hybrid models recover teacher performance" style="max-width:100%; height:auto; display:block; margin:0 auto;">
  <figcaption style="color:#666; font-size:0.95rem; margin-top:0.5rem;">
    <strong>Coverage as a function of preserved attention heads.</strong>
    Evaluated on retrieval-heavy and knowledge-focused tasks for Llama-1B and Qwen2-1.5B. k=0 is a pure SSM student; the full-head baseline is a Transformer distilled into a Transformer, isolating the effect of head selection from distillation itself.
  </figcaption>
</figure>

In both models, just 10 attention heads (roughly 2% of all heads) are enough to recover over 95% of the teacher's performance on retrieval-heavy tasks. Knowledge-focused tasks are largely unaffected throughout, confirming that the preserved heads are doing retrieval work specifically. Note also the sharp drop in retrieval performance below this threshold, revealing a critical point: a handful of heads are truly load-bearing, and once you drop below that floor, performance falls off quickly.

This is a much more extreme reduction than previous hybrids, which typically preserve 25% or more of attention heads. Why do most hybrids preserve so many then? Because they weren't designed with retrieval in mind and simply picked a ratio. Retrieval-Aware Distillation is the attempt to do this properly.

## If Attention Does Retrieval, What Are the SSMs Actually Doing?
If retrieval is handled entirely by a handful of attention heads, what work is left for the SSM layers? And does that remaining work require the same architectural capacity?

SSMs compress the past into a fixed-size vector (their recurrent state) which they update as each new token arrives. The size of this state (its dimension) controls how much information the SSM can carry forward. In a pure SSM, this state has to do everything: model local syntax and fluency, track discourse structure, and support any retrieval the model might need to perform. That's a lot to ask of a single fixed-size vector, and in practice it requires the state dimension to be set large enough to cover all the bases. But in our hybrid, retrieval has been handed off to the attention heads. The SSM is now free to focus on something narrower: local, short-range dependencies like syntax, fluency, and token-level coherence. If that's true, then a large recurrent state was partly a side-effect of the retrieval burden, and once that burden is lifted, the state can be shrunk.

To test this, we fix the top retrieval-critical attention heads and vary the SSM state dimension from 64 down to 4 --- a 16× reduction. As the figure below shows, performance on both retrieval-heavy and knowledge-focused tasks stays remarkably stable throughout up to an 8× reduction. Only at a 16× reduction does meaningful degradation appear.

<figure style="text-align:left; margin:1.25rem 0;">
  <img src="./state-size.png" alt="Reducing state size has minimal impact when retrieval is handled by attention." style="max-width:100%; height:auto; display:block; margin:0 auto;">
  <figcaption style="color:#666; font-size:0.95rem; margin-top:0.5rem;">
    <strong>Reducing state size has minimal impact when retrieval is handled by attention.</strong> We vary the SSM state dimension while keeping the top 10 and 20 retrieval-critical attention heads fixed. Performance stays stable down to an 8× reduction, and only degrades noticeably at 16×.
  </figcaption>
</figure>

This confirms that the state dimension was doing double duty before, serving both local modeling and implicit retrieval. Once those roles are separated, each component can be sized for its actual job --- and the SSM's actual job turns out to be considerably cheaper than the combined one.

This matters beyond theory too. While reducing KV-cache overhead is the main source of memory savings at long sequences, short sequences are common in practice, and there the SSM's recurrent state is a comparable or even larger contributor to total memory than the KV-cache. So if the state can indeed be shrunk, we get concrete memory savings across the board, not just at long sequences.

## So, What Have We Gained?

Starting from a pretrained Transformer, Retrieval-Aware Distillation produces a hybrid that preserves only 2% of attention heads rather than the 25% typical of prior hybrids, and shrinks the SSM state by 8×. To quantify the combined effect of fewer KV heads and a smaller SSM state, we break memory into two parts: a fixed state cost paid upfront by SSM heads regardless of sequence length, and a growing KV-cache cost paid by attention heads for every new token:

$$
M(L) = N_{\text{SSM}} \cdot d_{\text{head}} \cdot d_{\text{state}} \cdot 2 + N_{\text{KV}} \cdot d_{\text{head}} \cdot 4 \cdot L \quad \text{(bytes)}
$$

where \\(N_{\text{SSM}}\\) is the total number of SSM heads across all layers, \\(N_{\text{KV}}\\) is the total number of KV heads, \\(d_{\text{head}} = 64\\) is the head dimension, \\(d_{\text{state}}\\) is the SSM state size, and \\(L\\) is the sequence length. The first term is constant, paid once regardless of sequence length. The second grows linearly with \\(L\\).

Plugging in the numbers for each model at a sequence length of 10,000 tokens:
- **Pure Transformer** \\((N_{\text{SSM}}=0, N_{\text{KV}}=128)\\): \\(0 + 128 \cdot 64 \cdot 4 \cdot 10{,}000 \approx 320{,}000\\) KB
- **Standard 25% hybrid** \\((N_{\text{SSM}}=384, d_{\text{state}}=64, N_{\text{KV}}=32)\\): \\(3{,}072 + 8 \cdot 10{,}000 = 83{,}072\\) KB
- **Retrieval-Aware hybrid** \\((N_{\text{SSM}}=492, d_{\text{state}}=8, N_{\text{KV}}=10)\\): \\(492 + 2.5 \cdot 10{,}000 = 25{,}492\\) KB

At long sequences, where the KV-cache dominates, this is a 3–6× improvement over a standard hybrid, all while recovering over 95% of the teacher's performance on retrieval-heavy tasks.

<figure style="text-align:left; margin:1.25rem 0;">
  <img src="./memory-footprint.png" alt="Memory footprint comparison across sequence lengths" style="max-width:90%; height:auto; display:block; margin:0 auto;">
  <figcaption style="color:#666; font-size:0.95rem; margin-top:0.5rem;">
    <strong>Memory footprint as a function of sequence length.</strong>
The retrieval-aware hybrid yields a 3–6× memory reduction over a standard 25% hybrid across typical context lengths, thanks to fewer KV heads (shallower slope) and an 8× smaller SSM state (lower intercept). Note that both hybrids start above zero: unlike the pure Transformer, they maintain a fixed SSM state cost upfront, before the KV-cache begins to grow.
  </figcaption>
</figure>

# Conclusion

The Transformer-SSM gap turns out to be surprisingly narrow once you know where to look. Nearly all of it traces back to a handful of attention heads doing retrieval work that SSMs simply cannot replicate, and once you identify and preserve those heads, the rest of the network can be made dramatically leaner. Retrieval-Aware Distillation is essentially the formalization of that insight: *let function, not ratio, determine architecture*.

While the above results show that retrieval capability can be recovered with a fraction of the attention heads, two directions remain open.

**On distillation:** the head-knockout probe is simple and effective, but coarse. It measures retrieval importance in isolation, ignoring the fact that heads interact: removing one head may shift the importance of others, and jointly redundant heads might be safely pruned together. A finer-grained probe that accounts for these interactions, or that captures gradations of retrieval importance rather than just knockout sensitivity, could yield better hybrid architectures with even fewer preserved heads. It would also scale more gracefully to larger models, where running a full per-head ablation becomes expensive.

**On architecture:** perhaps the most ambitious direction is removing the pipeline entirely. Right now, Retrieval-Aware Distillation requires two stages: a trained Transformer teacher to probe, and a separate distillation run into the hybrid student. Could a model instead learn its own hybrid architecture during pretraining, discovering which heads should be attentive and which recurrent without any predefined structure or expensive teacher? That would turn retrieval-aware design from a post-hoc distillation recipe into a native property of the training process itself.

# References

1. Simran Arora, Sabri Eyuboglu, Aman Timalsina, Isys Johnson, Michael Poli, James Zou, Atri Rudra, and Christopher Ré. "Zoology: Measuring and Improving Recall in Efficient Language Models." arXiv preprint arXiv:2312.04927 (2023). <https://arxiv.org/abs/2312.04927>

2. Aviv Bick, Eric Xing, and Albert Gu. "Understanding the Skill Gap in Recurrent Language Models: The Role of the Gather-and-Aggregate Mechanism." arXiv preprint arXiv:2504.18574 (2025). <https://arxiv.org/abs/2504.18574>

3. Kimi Team. "Kimi Linear: An Expressive, Efficient Attention Architecture." arXiv preprint arXiv:2510.26692 (2025). <https://arxiv.org/abs/2510.26692>

4. Qwen Team. "Qwen3-Next: A New Generation of Ultra-Efficient Model Architecture Unveiled." Qwen Blog, September 11, 2025. <https://qwen.ai/blog?id=e34c4305036ce60d55a0791b170337c2b70ae51d>
