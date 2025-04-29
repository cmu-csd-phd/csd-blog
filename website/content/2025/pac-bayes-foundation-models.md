+++
# Classical generalization theory is more predictive in foundation models than in conventional deep networks
title = "Classical generalization theory is more predictive in foundation models than in conventional deep networks"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2025-04-28

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Artificial Intelligence", "Theory"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
# Consider these similar to keywords specified for a research paper.
tags = ["foundation-models", "pac-bayes", "generalization"]

[extra]
author = {name = "Victor Akinwande", url = "https://home.victorakinwande.com" }
# The committee specification is  a list of objects similar to the author.
committee = [
    {name = "Aviral Kumar", url = "https://aviralkumar2907.github.io"},
    {name = "Max Simchowitz", url = "https://msimchowitz.github.io"},
    {name = "Runtian Zhai", url = "https://www.runtianzhai.com"}
]
+++

**Key takeaway:** When learning over discrete prompts used in modern vision-language models, classical PAC-Bayes bounds turn out to be remarkably tight — significantly tighter than prior PAC-Bayes results on deep networks.

If you have ever tinkered with a large vision-language model (VLM), you might have noticed something odd. You can "engineer" a prompt — maybe even over-optimize it to your training data — and it still works well on the test set.

Wait, what? Is that not overfitting? Shouldn't the test performance crash?

Surprisingly, it doesn't. In this post, we'll explore *why prompt engineering tends to generalize*, even when it seems like it shouldn't — and how a classic theory of generalization (PAC-Bayes) gives us a satisfying explanation.

---

## Zero-shot Learning with CLIP

In zero-shot learning, we use **natural language prompts** (like “a photo of a dog”) to guide models like CLIP (Contrastive Language–Image Pretraining) in making predictions. We do not finetune, and there is no labeled training. Instead, we cleverly choose phrases that describe the concept we wish to classify.

CLIP is a vision-language model trained to align images and text in a shared embedding space. Formally, CLIP consists of two encoders:

- An image encoder: \\( f_\mathrm{img}: \mathcal{X} \rightarrow \mathbb{R}^d \\)
- A text encoder: \\( f_\mathrm{text}: \mathcal{T} \rightarrow \mathbb{R}^d \\)

Given a batch of image–text pairs \\( \{ (x_i, t_i) \}_{i=1}^n \\), CLIP is trained using a contrastive loss to maximize the cosine similarity between corresponding image and text embeddings:

$$
\begin{aligned}
L &= \frac{1}{2} \left( L_{\mathrm{img2text}} + L_{\mathrm{text2img}} \right) \\
\quad \text{where} \quad \\\\
L_{\mathrm{img2text}} &= -\frac{1}{N} \sum_{i=1}^{N} \log \frac{ \exp\left( \langle f_{\mathrm{img}}(x_i), f_{\mathrm{text}}(t_i) \rangle / \tau \right) }{ \sum\limits_{j=1}^{N} \exp\left( \langle f_{\mathrm{img}}(x_i), f_{\mathrm{text}}(t_j) \rangle / \tau \right) } \\\\
L_{\mathrm{text2img}} &= -\frac{1}{N} \sum_{i=1}^{N} \log \frac{ \exp\left( \langle f_{\mathrm{text}}(t_i), f_{\mathrm{img}}(x_i) \rangle / \tau \right) }{ \sum\limits_{j=1}^{N} \exp\left( \langle f_{\mathrm{text}}(t_i), f_{\mathrm{img}}(x_j) \rangle / \tau \right) }
\end{aligned}
$$


Where \\( \langle \cdot, \cdot \rangle \\) is **cosine similarity**, and \\( \tau \\) is a **temperature parameter**.

---

### Inference (Zero-shot Classification)

At inference time, for each class label \\( k \\), we define a natural language prompt \\( t_k \in \mathcal{T} \\) (e.g., `"a photo of a cat"`). To classify an image \\( x \\), we compute:

\\( \hat{y} = \arg\max_k \left\langle f_{\mathrm{img}}(x), f_{\mathrm{text}}(t_k) \right\rangle \\) where the maximization is over all possible class indices \\( k \\).

This allows CLIP to perform classification tasks **without labeled training data**, using only **textual descriptions** of the classes. Beyond classification, CLIP enables other tasks like retrieval and visual question answering. For example, given a query like “*a photo of a beach at sunset”*, CLIP can rank thousands of images by their similarity to this phrase.

In this post, we describe our study of zero-shot classification using CLIP models. In this context, we do not update the model weights and predictive performance comes entirely from the quality of the learned embeddings and the prompt itself. Zero-shot classifiers based on CLIP have been shown to be on par or perform even better than training vision models using supervised learning on large-scale image datasets.

### Prompt Engineering for CLIP Classification

In discriminative tasks like classification, prompt engineering (i.e., selecting specific text descriptions of the classes) becomes a way to steer the model toward task-relevant features. Since CLIP computes similarity between image and text embeddings, small changes in the wording of a prompt can meaningfully shift the decision boundary.

Admittedly, prompt engineering is more commonly used for generative tasks like image generation. However, our analysis is restricted to classification — and one can view discriminative tasks as a proxy for understanding the generative version of prompt engineering.

With this framing in mind, notions like overfitting to the training data by over-optimizing a prompt become plausible.

---

The central puzzle: if we optimize prompts on training data (e.g., via greedy search), why don't we overfit? And can we predict how well a prompt will do on test data?

We show that applying **PAC-Bayes theory** to the **space of discrete text prompts** provides an answer for this. **PAC-Bayes** is a classical framework that gives generalization guarantees by balancing:

- How well a model fits the training data (**empirical risk**), and
- How "simple" or "expected" it is, under a prior (**Occam's razor**).

---

## Framing Prompt Engineering as Learning

In our [paper](https://arxiv.org/abs/2310.03957), we frame prompt engineering as a learning problem within the PAC-Bayes framework. In this view, **each prompt corresponds to a hypothesis** — that is, a prompt defines a classifier, and the overall space of hypotheses is the discrete set of possible token sequences. The **prior** over this space is provided by a pretrained language model, such as LLaMA-7B, which naturally assigns higher probability to prompts that are natural, coherent text sequences. Once a specific prompt is chosen — for example, through a greedy search procedure — it becomes the **posterior**, represented as a point mass over the selected prompt. This setup allows us to compute a PAC-Bayes bound on generalization error that accounts both for empirical performance and the likelihood of the prompt under the language model prior.

With this setup, the PAC-Bayes bound becomes a concrete, computable upper bound on the expected test error of a prompt, based on its training error and its **log-probability under the language model**.

This turns the generalization problem into one of **regularized search**: find prompts that fit the data and are likely under the language model. While the number of possible token combinations is combinatorially large, natural language imposes strong semantic constraints. Another important constraint is the fixed context length of CLIP’s text encoder. In most implementations, this is **77 tokens**, including special tokens like the end-of-text marker. This limit puts a hard cap on the size of the hypothesis space we can search over: any learned prompt must fit within this token budget.

---

## A Classical Bound That Works in Practice

Let's write the bound more precisely. Given a prior \\( P(\theta) \\) over prompts \\( \theta \\), and a learned prompt \\( \hat{\theta} \\), the PAC-Bayes bound states (adapted from [McAllester 1999](#mcallester)):

$$
R(\hat{\theta}) \leq r(\hat{\theta}) + \frac{\mathrm{KL}(\hat{\theta} \Vert P) + \log\left( \frac{1}{\delta} \right) + 2}{2n - 1}
$$

Where:

- \\( R(\hat{\theta}) \\) is the expected test error,
- \\( r(\hat{\theta}) \\) is the empirical (training) error,
- \\( \mathrm{KL} \\) is the Kullback–Leibler divergence between the posterior and the prior,
- \\( n \\) is the number of training samples,
- \\( \delta \\) is a confidence parameter.

In the case of a point-mass posterior (i.e., a deterministic prompt \\( \hat{\theta} \\)), the \\( \mathrm{KL} \\) divergence term simplifies to the **negative log-probability** of the prompt under the prior — making it computable and interpretable.

Crucially, the theory teaches us not simply to minimize the empirical error \\( r(\hat{\theta}) \\), but to minimize a trade-off between the empirical error and complexity (captured by the PAC-Bayes term). A prompt \\( \hat{\theta} \\) with slightly higher training error but significantly low complexity can have a smaller bound — and hence better generalization — than a prompt with the absolute lowest training error. Formally the best prompt is the one minimising the bound: \\( r(\hat{\theta}) + \frac{\mathrm{KL}(\hat{\theta} \Vert P) + \log\left( \frac{1}{\delta} \right) + 2}{2n - 1} \\) rather than \\( r(\hat{\theta}) \\) alone.

---

## Tight Bounds in Practice

<!-- ![Test error vs. PAC-Bayes bound for prompts on CIFAR-10, CIFAR-100, and OfficeHome datasets. The data points lie close to the y = x line, showing tight correspondence.](./bound.png) -->

<figure style="width:80%; margin:auto; text-align:center;">
    <img style="width:100%; display:block; margin:auto;" src="./bound.png" alt="Test error vs. PAC-Bayes bound for prompts on CIFAR-10, CIFAR-100, and OfficeHome datasets. The data points lie close to the y = x line, showing tight correspondence."></img>
    <figcaption style="margin-top:10px;">Test error vs. PAC-Bayes bound for prompts on CIFAR-10, CIFAR-100, and OfficeHome datasets. The data points lie close to the y = x line, showing tight correspondence.</figcaption>
</figure>

<!-- Test error vs. PAC-Bayes bound for prompts on CIFAR-10, CIFAR-100, and OfficeHome datasets. The data points lie close to the y = x line, showing tight correspondence. -->

In our experiments, we perform prompt search using simple greedy algorithms. Starting from an (optional) initial token (e.g., `"a photo of"`), we iteratively select the next token that most improves performance on the training set. At each step, we evaluate candidate continuations by measuring classification accuracy using the CLIP similarity score.

When this approach is applied in practice, the results are surprising. Across image-classification datasets like CIFAR-10, CIFAR-100, and ImageNet, the PAC-Bayes bounds are not only non-vacuous — they are remarkably **tight**, sometimes within **2–6%** of the actual test error. For instance, on CIFAR-10, a prompt found via greedy search has a training error of 2.3%, a test error of 2.8%, and a PAC-Bayes bound of just 8.6%. On ImageNet, with a much larger class set, the bound is still within 6% of the test error.

This level of tightness is exceptional in the context of deep learning, where most generalization bounds are either loose or vacuous. Furthermore, we see that if we simply assign a uniform probability (i.e. uniform convergence) to every prompt, we obtain looser bounds.

Importantly, these bounds are computed **without needing data-dependent priors**, that is we don't use a validation set to improve the prior — just using a language model prior and a discrete prompt space suffices.

---

## Why Prompts Generalize

Unlike neural network weights, prompts are selected from a **structured, and discrete** space — the set of token sequences. Even if this space is searched greedily to reduce the training error \\( r(\hat{\theta}) \\), CLIP itself favours natural, compressible prompts. Although greedy prompt optimization does not explicitly regularize the KL divergence or complexity term, it still tends to generalize well because the complexity of the prompts themselves is constrained. This beneficial regularization effect is captured explicitly by our bound.

In addition, even without being used during optimization, the language model informs which prompts are more likely to be compressible, and we use it within the PAC-Bayes framework to show that the greedy result lies within a "low-complexity" region.

Finally, we make this more explicit and guide the search toward hypotheses that generalize better by incorporating the KL term into the greedy search optimization. We provide the details of this result in the paper.

---

The robustness of this behavior becomes even more evident when we intentionally corrupt the training labels. In this setup, we randomly flip a fraction of the class labels, effectively injecting noise into the data. If prompt engineering were prone to overfitting, we might expect it to memorize these noisy labels — achieving low training error but poor test accuracy, much like large neural networks often do. However, we observe something different: as we increase the amount of noise, both training and test accuracy drop in tandem. In other words, prompts obtained via Greedy fail to memorize random labels — and generalization degrades smoothly alongside training performance.

This behavior points to a fundamental property of the prompt-based learning setup: the space of prompts has limited capacity to memorize arbitrary data, providing a form of regularization that constrains its ability to overfit.


<figure style="width:60%; margin:auto; text-align:center;">
    <img style="width:100%; display:block; margin:auto;" src="./memorize.png" alt="Left: We show that as the proportion of random labels increases, both training and test accuracy of prompts degrade together. Right: We show that a greedy prompt learning on CIFAR-10 yields small generalization error even with small sample sizes."></img>
    <figcaption style="margin-top:10px;">Left: We show that as the proportion of random labels increases, both training and test accuracy of prompts degrade together. Right: We show that a greedy prompt learning on CIFAR-10 yields small generalization error even with small sample sizes.</figcaption>
</figure>

In addition, when the number of data points is small (e.g., \\( n = 20 \\)), the use of PAC-Bayes is especially attractive since we can use *all* the data points to estimate the posterior and bound its risk.

In contrast to typical deep learning bounds — which degrade rapidly with small sample sizes — PAC-Bayes bounds remain non-vacuous even with only 20 labeled examples per class on CIFAR-10.

---

## A Model Selection Tool

**The prompts with the tightest PAC-Bayes bounds tend to have the best test performance.**

This makes the bound useful not just for analysis, but also for prompt selection. When multiple prompts perform similarly on the training set, we can pick the one with the smallest bound — effectively combining empirical fit with a regularization term.

<!-- ![When we compare test error against train error or the generalization bound, we observe prompts with the tightest PAC-Bayes bounds tend to have the best test performance.](./selection.png) -->
<figure style="width:80%; margin:auto; text-align:center;">
    <img style="width:100%; display:block; margin:auto;" src="./selection.png" alt="When we compare test error against train error or the generalization bound, we observe prompts with the tightest PAC-Bayes bounds tend to have the best test performance."></img>
    <figcaption style="margin-top:10px;">When we compare test error against train error or the generalization bound, we observe prompts with the tightest PAC-Bayes bounds tend to have the best test performance.</figcaption>
</figure>

---

## Conclusion: Prompt Engineering is Theoretically Sound

Prompt engineering is not just a practical hack — it's a well-founded method with **provable generalization guarantees**. These findings suggest a broader lesson: generalization in deep learning may be easier to understand in discrete, structured hypothesis spaces, like that of natural language prompts. In particular, at the scale of large foundation models, we enter into a regime where classical notions of compression and generalization work.

Rather than requiring entirely new theoretical tools, the use of pretrained language models as priors, combined with the discrete structure of prompts, enables PAC-Bayes bounds that are tighter than anything previously achieved in large-scale vision tasks.

---

## Reference

<a name="paper">Victor Akinwande, Yiding Jiang, Dylan Sam, J. Zico Kolter. *Understanding prompt engineering may not require rethinking generalization*. ICLR 2024</a>

<a id="mcallester" name="mcallester">David A McAllester. *PAC-Bayesian model averaging*. In Proceedings of the twelfth annual conference on Computational learning theory, pp. 164–170, 1999</a>
