+++
title = "Learning by Analogy for Compositional Generation"
date = 2026-04-30

[taxonomies]
areas = ["Artificial Intelligence", "Theory"]
tags = ["compositional generalization", "diffusion models", "text-to-image generation", "causality", "hierarchical models"]

[extra]
author = {name = "Lingjing Kong", url = "https://lingjing-kong.github.io/"}
committee = [
  {name = "Weina Wang", url = "https://www.cs.cmu.edu/~weinaw/"},
  {name = "Mingkuan Xu", url = "https://mingkuan.taichi.graphics/"},
  {name = "Minchen Li", url = "https://www.cs.cmu.edu/~minchenl/"},
]
+++

Suppose I ask a text-to-image model for *a peacock eating rice*. The model may know what a peacock looks like. It may know what rice looks like. It may even know how a chicken pecks at rice. But if the training data never contained the exact composition *peacock + rice*, why should the model know how to combine those pieces correctly?

Humans do this kind of extrapolation all the time. Even if I have never seen a peacock eating rice, I can still picture it. I can compare peacocks to chickens, notice that both have beaks, and transfer what I know about a chicken pecking at rice to a new bird. In other words, I can reason by **analogy**.

This is the central challenge of **compositional generalization**: can a model produce a novel combination of familiar concepts, even when that exact combination was missing from training? In this post, I will describe a causal and hierarchical view of compositional generalization inspired by analogy-making (Gentner, 1983; Holyoak and Thagard, 1989). The main message is simple:

> A model can generalize compositionally when it learns reusable low-level modules and knows how to recombine them in new settings.

That statement sounds intuitive, but it turns out to have both a precise theoretical form and a practical implementation in diffusion models.

![A diagram showing how the unseen scene "peacock eating rice" can be composed by combining low-level modules shared across the seen examples "peacock" and "chicken eating rice."](./teaser.jpg)

*Figure 1. A running example for the whole post. The unseen composition “peacock eating rice” can be formed by transferring low-level modules—especially the “beak interacting with rice” behavior—from related seen examples.*

# The Problem with Unseen Combinations

A modern text-to-image model is trained on pairs of text and images. At training time, it only sees part of the full space of possible concept combinations. A dataset might contain many pictures of peacocks, many pictures of rice, and even pictures of chickens eating rice, but still contain no picture of a peacock eating rice.

This creates an **out-of-support** problem. On the combinations that do appear in training, a model can simply fit the data. But once we move to a missing combination, success depends on whether the model has learned a representation that is structured in the right way. If it has not, then the output for the unseen prompt is effectively unconstrained.

Why is this hard? One reason is that natural images are full of interactions. A scene is not just a bag of isolated concepts that add together independently. Objects have parts, attributes, poses, and relations. “Eating rice” is not a global property smeared evenly across the image; it is a local interaction involving a bird’s head, beak, posture, and the food on the ground. A model that treats concepts as independent or purely additive may miss exactly the structure that makes transfer possible.

This observation helps explain a gap between theory and practice. Some existing theoretical accounts of compositionality assume very simple interactions, such as concepts affecting disjoint image regions or combining additively in pixel space (for example, Lachapelle et al., 2023; Brady et al., 2023, 2024). Those assumptions are mathematically convenient, but they do not fully capture the kinds of structured interactions we care about in real images. If a model is going to imagine a new scene, it needs a way to reuse fine-grained interaction patterns—not just whole objects.

So the real question is not merely “can we mix concepts?” It is:

> **What latent structure makes recombination possible in the first place?**

# Analogy Suggests Two Principles

The underlying work starts from a cognitive intuition: people often achieve compositional generalization by drawing analogies. The peacock example is useful because it makes the mechanism vivid.

When I compare a peacock to a chicken, I do not treat them as unrelated atomic labels. I break them into parts and properties. Both have beaks. Both have wings. Both have feet. They differ in some features too: the peacock has a colorful tail, while the chicken has a cockscomb. That comparison suggests two general principles.

The first is **modularity**. Complex concepts can be decomposed into reusable pieces. A peacock is not one indivisible unit; it is built from lower-level modules such as beak, wings, and tail. Importantly, interactions can also be modular. The way a beak interacts with rice—pecking—is itself a reusable piece of structure.

The second is **minimal change**. Closely related high-level concepts often share most of their lower-level structure and differ only in a small number of details. Peacock and chicken are much closer to each other than either is to a fish because they share many low-level modules. That overlap is precisely what makes analogical transfer plausible.

Together, these principles suggest a recipe for composition. To generate *peacock eating rice*, keep the modules that define peacock, keep the interaction pattern that explains how a chicken eats rice, and change as little else as possible. You do not need a training example containing the whole scene. You only need the relevant low-level ingredients to have appeared somewhere.

This viewpoint differs from a purely symbolic notion of composition. The reusable pieces are not just words or object IDs. They are latent variables that represent attributes, parts, and interactions at different levels of granularity.

# A Hierarchical Causal Model

To formalize this intuition, the paper introduces a **hierarchical latent data-generating process** grounded in causal ideas about modular mechanisms and invariance (Pearl, 2009; Peters, Janzing, and Schölkopf, 2017). At the top of the hierarchy are high-level concepts, such as the entities named in the text prompt. Lower in the hierarchy are more fine-grained concepts: parts, attributes, and interaction modules. At the bottom sits the image itself.

You can think of the hierarchy as a causal graph. High-level concepts influence lower-level ones, which in turn influence the observed pixels. For our running example, a high-level concept like “peacock” can activate lower-level variables corresponding to beak, wings, feet, and colorful tail. A prompt involving rice can activate modules describing grains on the ground. A further low-level interaction variable can encode the relation between a beak and the rice.

The important point is that the model is **not** forced to treat each training example as a monolithic whole. Instead, it can represent what is shared across examples and what is unique to each one.

## When should composition work?

The paper’s first main theoretical result gives a clean intuition for when an unseen composition should be possible.

> **Plain-English version of the theorem.** A new concept combination is composable if every low-level module it needs has already been supported by *some* training example. Different modules may come from different examples.

That last sentence is the key. A model does **not** need one training example that contains everything. It can learn the “colorful tail” module from images of peacocks, the “beak interacting with rice” module from images of chickens eating rice, and then combine them to generate a peacock eating rice.

This is what makes the framework more flexible than earlier theories based on disjoint image regions or simple additive interactions. The lower-level modules in the hierarchy can be shared, reused, and combined in nontrivial ways. The interaction “beak and rice” is not forced to be a polynomial term or a fixed hand-designed interaction class. It is a learned causal module.

The theory also explains why sparse structure helps. If each lower-level variable depends on only a small number of parents, then there are fewer ingredients that must have been seen before. Compositional transfer becomes easier when the system is built from small, reusable pieces.

## Can we actually learn the hierarchy?

A nice theory would be much less interesting if it only said what an ideal latent structure looks like. The second main result of the paper goes further: under suitable assumptions, this hierarchical structure is **identifiable** from observable data such as text-image pairs.

In rough terms, identifiability means that a learned representation can recover the underlying latent variables **component-wise**, up to standard ambiguities such as permutation and invertible reparameterization. That is much stronger than merely recovering a mixed subspace containing several concepts at once. If “beak” and “tail” are irreversibly entangled in the representation, then modular transfer becomes difficult.

The assumptions behind the result are technical but intuitive:

1. The image preserves the information in the latent variables.
2. The conditional distributions in the hierarchy are smooth.
3. Variables at the same level become dependent only because of higher-level causes.
4. Distinct children respond differently when their parents vary.

The last condition is especially important. If every lower-level concept changed in exactly the same way as its parents changed, there would be no statistical signal allowing us to separate them. The paper uses this variability to identify one level at a time, starting from the high-level concepts provided by the text and working downward through the hierarchy.

Conceptually, this result matters because it closes a loop. The paper does not just propose a latent structure that would be *nice to have*. It argues that the structure can, in principle, be learned from the kind of data we already collect.

# Turning the Theory into a Diffusion Model

So far the story has been abstract. The next step is to convert the theory into something a text-to-image model can actually use.

The paper’s empirical implementation, called **HierDiff**, is built on a simple observation about diffusion models such as Stable Diffusion (Rombach et al., 2022). A diffusion model generates an image by denoising step by step, from heavy noise to a clean sample. Early denoising steps determine the broad global structure of the scene. Later steps fill in fine local detail. That already sounds like a hierarchy.

The core design decision is therefore to match the conditioning information to the denoising step.

- At **high-noise** steps, use the **global prompt** to determine the overall scene.
- At **low-noise** steps, inject **local descriptions** that specify the parts, attributes, and interactions needed for fine detail.

To get those local descriptions, HierDiff starts from the original prompt and uses a language model to decompose it into several lower-level textual descriptions. For example, from “a chicken eating rice,” it might produce local descriptions for the chicken, the rice, and the surrounding scene.

Then it combines global and local conditioning through a time-dependent cross-attention rule:

$$
A_t = (1-s(t)) A_{\text{global}} + s(t) A_{\text{local}},
$$

where the schedule \\(s(t)\\) shifts the model from coarse global reasoning toward fine local reasoning as denoising progresses.

![A diagram of HierDiff. The method decomposes a global prompt into several local descriptions, encodes them, interpolates between global and local cross-attention over denoising steps, and adds a regularizer to keep local attention maps from overlapping too much.](./method.png)

*Figure 2. HierDiff interprets diffusion time as a hierarchy: global information dominates earlier steps, while local concept descriptions matter more later in generation.*

The second design decision comes directly from the theory’s emphasis on sparse, reusable modules. If the local attention maps for different descriptions overlap too much, then the model may blur their roles together. To prevent that, HierDiff adds a sparsity-style regularizer that discourages unnecessary overlap between local attention maps. Intuitively, the “beer bottle” description should not cover the same region as the “pineapple” description unless the prompt truly requires it.

So the method is remarkably aligned with the theory:

- **Hierarchy** becomes time-dependent conditioning across diffusion steps.
- **Modularity** becomes decomposition into local textual concepts.
- **Sparse interactions** become an explicit overlap penalty on attention maps.

# What the Experiments Show

The paper fine-tunes the method from Stable Diffusion 1.5 (Rombach et al., 2022), following prior work such as ELLA that replaces the text encoder with FLAN-T5-XL for stronger text understanding (Hu et al., 2024). During training it uses a dataset that provides both the global description and aligned local descriptions. At test time, it uses Qwen2.5 to generate local descriptions from the user’s original prompt (Yang et al., 2024).

The headline result is that these theoretically motivated choices translate into substantially better compositional generation. On **DPG-Bench**, a benchmark designed to stress difficult prompts with multiple objects, attributes, and relations (Hu et al., 2024), HierDiff reaches a score of **79.28**, compared with **74.91** for ELLA and **63.18** for baseline Stable Diffusion 1.5 in the paper’s setup.

Just as important, the gains are not concentrated in a single category. The benchmark separately scores **Global**, **Entity**, **Attribute**, **Relation**, and **Other**, and HierDiff improves all of them. That is exactly what one would hope from the theory: the hierarchy should help with global organization, while modular local conditioning should help with entities, attributes, and relations.

![Examples from the paper comparing Stable Diffusion 1.5, ELLA, and HierDiff on difficult prompts involving multiple entities and relations.](./experiments_1.png)

*Figure 3. In these examples, the baseline models often drop objects, confuse attributes, or miss relations, while HierDiff more faithfully assembles the requested scene.*

The qualitative examples are also informative. In one prompt, HierDiff correctly produces a **sleek black rectangular keyboard** on a beige carpet, while the baselines miss the keyboard entirely. In others, it handles combinations such as worn brown boots with blue balloons, the Sydney Opera House beside the Eiffel Tower, or a pyramid-shaped tablet placed near a crescent-shaped swing. These are exactly the sorts of prompts where “bag of words” conditioning tends to fail.

The ablations help explain why. If the model removes the **time-dependent hierarchy**, performance drops and generations become globally confused. If it removes the **sparsity regularization**, local concepts bleed into one another and attention maps overlap excessively. The combination of both ingredients gives the best overall behavior.

![An ablation from the paper. Without time-dependent conditioning the model confuses the relation among objects; without sparsity regularization the attention maps for local concepts overlap too much.](./ablation.jpg)

*Figure 4. The two design choices matter for different reasons: time dependence improves global relational understanding, while sparsity improves local disentanglement and control.*

The paper also visualizes the local attention maps across denoising steps. Early in generation, the attention is broad and global; later, it sharpens into localized regions associated with specific lower-level descriptions such as “chicken” and “rice.” That is precisely the hierarchical behavior the method was designed to induce.

![A visualization from the paper showing that local attention maps become more focused over denoising steps, moving from global structure toward localized concepts such as the chicken and the rice.](./diffusion_step_attn.png)

*Figure 5. As denoising proceeds, the model’s local attention shifts from diffuse global structure to sharply localized concept regions, matching the hierarchy predicted by the theory.*

Finally, the implementation is not limited to a small backbone. The paper reports that a diffusion-transformer version with 4.8B parameters reaches **84.9** on DPG-Bench, competitive with larger modern systems listed in the paper, including DALL-E 3, SD3-medium, FLUX variants, and SANA.

# Why This Perspective Matters

One way to read this work is as a text-to-image paper that improves a benchmark score. But I think the more interesting lesson is methodological.

A lot of progress in generative modeling comes from scaling: larger models, larger datasets, and more compute. Scaling clearly matters. But when a task requires extrapolating to new combinations, the right **inductive bias** matters too. This paper argues that an especially useful bias is to organize representations around **shared, sparse, hierarchical modules**.

That viewpoint may extend beyond image generation. Any system that has to recombine concepts in new ways—multimodal reasoning, robotics, structured world modeling, or agentic planning—faces some version of the same challenge. If the representation is monolithic, transfer is brittle. If it is modular but shallow, it may miss interactions. A hierarchy offers a middle ground: it can represent rich interactions while still exposing reusable pieces.

The work also has limitations, and those are worth stating clearly. The identification theory assumes, among other things, that variables at the same hierarchical level do not directly cause one another; instead their dependence is explained by higher-level causes. That may be too restrictive for some real data. On the practical side, the quality of the local textual decomposition depends on the language model that generates it. If the prompt is broken into the wrong pieces, the benefits of hierarchical conditioning may shrink.

Still, I find the overall picture compelling. The paper gives a concrete answer to a question that often remains vague in machine learning discussions: **what kind of hidden structure actually makes compositional generalization possible?** Its answer is not “just bigger models” or “just better prompting.” It is that composition works when a system learns how to break concepts apart, recognize what can be reused, and recombine those modules with minimal interference.

That is, in a very literal sense, learning by analogy.

# References and Further Reading

This post is based on *Learning by Analogy: A Causal Framework for Composition Generalization*.

For readers who want more background, these references are a good starting point:

- Dedre Gentner. *Structure-Mapping: A Theoretical Framework for Analogy*. Cognitive Science, 1983.
- Keith Holyoak and Paul Thagard. *Analogical Mapping by Constraint Satisfaction*. Cognitive Science, 1989.
- Judea Pearl. *Causal Inference in Statistics: An Overview*. Statistics Surveys, 2009.
- Jonas Peters, Dominik Janzing, and Bernhard Schölkopf. *Elements of Causal Inference*. MIT Press, 2017.
- Robin Rombach et al. *High-Resolution Image Synthesis with Latent Diffusion Models*. CVPR, 2022.
- Xiwei Hu et al. *ELLA: Equip Diffusion Models with LLM for Enhanced Semantic Alignment*. 2024.
- Sébastien Lachapelle et al. *Additive Decoders for Latent Variables Identification and Cartesian-Product Extrapolation*. 2023.
- Jack Brady et al. *Provably Learning Object-Centric Representations*. 2023.
- Jack Brady et al. *Interaction Asymmetry: A General Principle for Learning Composable Abstractions*. 2024.
- An Yang et al. *Qwen2.5 Technical Report*. 2024.
