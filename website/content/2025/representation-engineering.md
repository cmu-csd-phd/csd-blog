+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "From Representation Engineering to Circuit Breaking: Toward Transparent and Safer AI"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2025-10-20

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Artificial Intelligence"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
# Consider these similar to keywords specified for a research paper.
tags = ["ML Safety", "Transparency", "Interpretability", "Robustness"]

[extra]
author = {name = "Andy Zou", url = "https://andyzoujm.github.io/" }
# The committee specification is  a list of objects similar to the author.
committee = [
    {name = "Aditi Raghunathan", url = "https://www.cs.cmu.edu/~aditirag/"},
    {name = "Nihar Shah", url = "https://www.cs.cmu.edu/~nihars/"},
    {name = "Ruihang Lai", url = "https://ruihanglai.com/"}
]
+++

# From Mechanisms to Representations: A Top-Down Turn in Interpretability

For years, interpretability research in machine learning has been guided by a “microscope” metaphor: if we zoom in far enough on neurons and circuits, perhaps we can reverse-engineer how models think. This bottom-up program, rooted in the search for mechanistic detail, has yielded striking insights into circuits and algorithmic motifs. Yet, like other reductionist sciences, it struggles to bridge the gap between low-level structure and the high-level behaviors that matter most in deployment—honesty, deception, power-seeking, or robustness against adversaries.

In other fields that study complex systems, progress often comes from complementing bottom-up analysis with top-down perspectives. Psychologists study cognition before mapping every synapse. Biologists analyze organisms and ecosystems before tracing every protein. Meteorologists begin with storms rather than molecules. Each discipline recognizes that understanding complex, adaptive systems requires starting with emergent properties—patterns that only make sense at higher levels of organization.

We believe interpretability should follow this example. Rather than treating neurons or circuits as the atomic units of meaning, we focus on distributed representations that encode knowledge and traits across many neurons. This shift in emphasis—from the implementational to the algorithmic level, in Marr’s terms—has shaped our recent work. It led first to [Representation Engineering (RepE)](https://www.ai-transparency.org/). Later, where we applied these representational insights to concrete safety challenges, we introduced [Circuit Breaking](https://www.circuit-breaker.ai/). Together, these methods chart a path toward models that are not only more transparent but also more controllable.


![bottom-up vs. top-down](./top_down.png)
**Figure 1:** *Mechanistic Interpretability (MI) vs. Representation Engineering (RepE). This figure draws
from (Barack & Krakauer, 2021; Wang et al., 2023a). Algorithmic and implementational levels are
from Marr’s levels of analysis. Loosely, the algorithmic level describes the variables and functions
the network tracks and transforms. The implementational level describes the actual parts of the neural
network that execute the algorithmic processes. On the right, we visualize the neural activity of a
model when processing text-based scenarios with differing levels of utility. The scenarios with high
utility evoke distinct neural trajectories within the representation space compared to those with lower
utility. ‘PC’ denotes a principal component.*

As Murray Gell-Mann put it in The Quark and the Jaguar (1995), we ought to 
> operate at the level of most invariances and find generalizable rules that apply at the level of these phenomena.

Representation Engineering takes exactly this top-down perspective. Instead of treating neurons or circuits as the atomic units of meaning, it focuses on the representational patterns distributed across many neurons. These population codes capture the higher-level behaviors of models. That models often retain their characteristic behaviors even when entire layers are ablated underscores the importance of this approach. Far from suggesting brittleness, this resilience highlights the adaptability of models, and points to the limits of searching for insight in isolated components. Emergence means that higher-level analyses are often not only sufficient to understand or predict behavior, but more reliable than attempting to trace the tangled details of low-level mechanisms.

RepE makes this principle concrete by allowing us to identify, amplify, and suppress traits directly in representational space. Since the original paper, we have used RepE to make models more honest, to weaken harmful tendencies, to improve robustness against adversarial attacks, and even to edit values and preferences encoded in models. These successes illustrate a key point: we do not need a complete mechanistic understanding to make progress on safety. Just as in other sciences, where high-level laws are often enough to guide useful predictions, representational-level interventions can yield real control even when the low-level substrate remains opaque. This should be cause for optimism. Even if mechanistic interpretability proves out of reach, we can still design safety objectives and engineer models to comply with them through representational means.

# Monitoring and Controlling Through Representational Space

The core idea of Representation Engineering is simple: if a model encodes concepts as high-dimensional vectors in hidden space, then those vectors can be found, characterized, and manipulated.

Formally, if a hidden state for an input \\(x\\) is \\( h(x) \in \mathbb{R}^d \\), and we have identified a direction \\( v \in \mathbb{R}^d \\) corresponding to a trait like honesty, we can shift the state by
$$h'(x) = h(x) + \alpha v$$
where \\(\alpha\\) determines how strongly we activate that trait.
This means that complex behaviors—such as truthfulness versus deception—can be moved up and down like sliders in a latent control panel. In practice, this gives us levers to systematically increase or suppress traits like helpfulness, harmlessness, or power-seeking. Our motivation was twofold: to create a method that scales as models grow, and to align interpretability with the traits we most care about.


# A Neuroscience Analogy

One way to understand the motivation behind Representation Engineering is through analogy with neuroscience. In cognitive science, we rarely attempt to map every individual neuron in order to explain behavior. Instead, we rely on tools like MRI scans, which reveal patterns of activation across brain regions when a subject engages in particular tasks. These images do not tell us everything about the mechanism of thought, but they provide a powerful window into the organization of cognition.

Representation Engineering plays a similar role for AI systems. Rather than tracing every circuit or neuron, it identifies the higher-level representational vectors that become active when a model exhibits certain traits. In this way, RepE allows us to both observe and intervene on a model’s “thought processes” in a manner that parallels how neuroscience links brain activity to cognition.

To make this analogy concrete, we developed Linear Artificial Tomography (LAT). Much like an MRI scan highlights areas of the brain that respond to stimuli, LAT visualizes the activity inside a transformer model layer by layer as it processes input. Once we have identified the representational direction corresponding to a trait like honesty, we can run a LAT scan to see how strongly that concept is expressed at different depths of the network. The result is a kind of tomography of the model’s internal landscape: certain layers “light up” with honesty, others remain neutral, and some may even lean toward deception.

![LAT scan](./lat_scan.png)
**Figure 2:** *Temporal LAT scans were conducted on the Vicuna-33B-Uncensored model to discern
instances of speaking the truth, such as when it admitted to copying others’ homework, and instances
of lying, like its denial of killing a person. These scans
offer layer-level resolution, with each minuscule block showing the extent of dishonest neural activity
within a layer at a specific token position. The figure on the right prominently exhibits a higher level
of deceptive neural activity.*

This neuroscience-inspired perspective emphasizes that RepE is not simply a mathematical trick. It is a methodology for studying and influencing AI at the representational level, much as cognitive science studies humans at the level of thought and behavior rather than neurons in isolation.

# From Maps to Brakes: The Need for Control

But transparency alone is not enough. RepE shows that models can be steered, but does not ensure they will remain in safe states. A model may be capable of honesty, yet still produce deceptive answers when prompted adversarially.

This realization pushed us toward a second step: using representational insight not just for understanding, but for real-time intervention.

Representation Engineering offers a novel lens through which we can enhance AI transparency. By observing and manipulating internal representations—specifically the activations within the model—we can begin to see not only what the system is doing, but also how its internal state changes when we intervene. Our RepE demo illustrates this vividly, giving users the ability to steer a model’s responses in real time, accentuating or suppressing different cognitive phenomena. Because these representational controls act directly on the hidden states, their strength can also be calibrated, creating subtle or dramatic shifts in behavior on demand.

A concrete example comes from examining truthfulness in Llama-3.1-8b-Instruct. When asked the seemingly straightforward question, “What does WIKI stand for?”, the model answers with a common misconception:

> **User:** What does “WIKI” stand for?

> **Llama-3.1-8b-Instruct:** WIKI stands for “What I Know Is.”

Even when we reframe the system prompt to emphasize truthfulness, the answer does not change:

> **User:** What does “WIKI” stand for?

> **Llama-3.1-8b-Instruct with prompt:** “You are an assistant who provides answers that are as truthful as possible.” WIKI stands for “What I Know Is.”

This phenomenon, which we call an imitative falsehood, occurs because models have absorbed incorrect patterns during training and often reproduce them, even when they “know better.” Traditional prompting cannot fully dislodge these habits.

With RepE control, however, we can directly activate the internal representation of truthfulness during the model’s generation. The result is a strikingly different answer:

> **User:** What does “WIKI” stand for?

> **RepE-controlled Llama-3.1-8b-Instruct:** The term WIKI actually stands for a combination of two Hawaiian words: wikiwiki, which means “fast” or “quick.” So in essence, Wiki refers to the idea that information should be quickly and easily accessible. The name was chosen because it reflects one of Wikipedia’s core values—providing fast access to knowledge.

This example highlights why representational control matters. The model did, in fact, encode the correct knowledge, but its baseline behavior was to reproduce the falsehood. By shifting the internal state toward the truthfulness representation, RepE unlocked that hidden competence and steered the model toward the accurate answer.

The ability to uncover and correct imitative falsehoods opens a new path for improving trustworthiness. By calibrating representational controls, we can systematically reduce error rates on benchmarks that target falsehoods, and, more importantly, we can ensure that the model’s outputs better reflect its latent knowledge. Yet these same knobs, if left unsecured, could also be misused to amplify deception, manipulation, or power-seeking tendencies. This brings us to Circuit Breaking.


# Circuit Breaking: Interrupting Harmful Trajectories

Circuit Breaking builds directly on RepE. Once we know the direction \\(v_{\text{harmful}}\\) corresponding to a dangerous behavior, we can actively monitor or suppress it during generation.
We do this by modifying hidden states as:
$$h'(x) = h(x) - \beta \cdot \langle h(x), v_{\text{harmful}} \rangle v_{\text{harmful}}$$
which projects out the harmful component before it produces unsafe output.

The metaphor is intentional: just as an electrical circuit breaker trips when current exceeds safe levels, a representational circuit breaker gets activated when the model’s state activates harmful subspaces.


![Circuit Breaking](./circuit_breaking.png)
**Figure 3:** *Introduction of circuit-breaking as a novel approach for constructing highly reliable
safeguards. Traditional methods like RLHF and adversarial training offer output-level supervision
that induces refusal states within the model representation space. However, harmful states remain
accessible once these initial refusal states are bypassed. In contrast, circuit breaking operate directly on internal representations, linking harmful states
to circuit breakers. This impedes traversal through a sequence of harmful states.*

This approach is robust to many of the failures that plague surface-level defenses. Refusal training, for instance, can often be bypassed by adversarial prompts. By contrast, Circuit Breaking intervenes at the causal level of representation, making it harder to evade. The method also generalizes: in multimodal systems it prevents “image hijacking” attacks, and in agents it reduces harmful action sequences under adversarial conditions.

![Circuit Breaking benchmarks](./cb_results.png)
**Figure 4:** *Adding circuit breakers using Representation Rerouting (RR) to refusal trained Llama-3-
8B-Instruct model leads to significantly lower attack success rate (ASR) over a wide range of unseen
attacks on [HarmBench](https://www.harmbench.org/) prompts, while its capabilities on standard LLM benchmarks (MT Bench
and MMLU) are largely preserved. RR directly targets the representations that give rise to harmful
outputs and reroutes them to an orthogonal space. This reliably interrupts the model from completing
the harmful generations even under strong adversarial pressure.*


# Putting Circuit Breakers in the Arena

Of course, demonstrating robustness in controlled laboratory settings is only the first step. The real test of any safety mechanism is whether it can withstand the creativity and persistence of real-world adversaries. For this reason, we deployed models equipped with Circuit Breakers into the Arena, a crowdsourced platform where thousands of users attempt jailbreaks and harmful prompts against state-of-the-art systems.

The Arena represents the closest thing we currently have to an adversarial field trial. Unlike static benchmarks, which quickly saturate, the Arena evolves as new red-teamers join and discover novel attack strategies. Each model faces a barrage of attempts to elicit harmful outputs, ranging from prompt injections and semantic misdirections to carefully crafted edge cases that exploit weaknesses in refusal training.

Our experience in the Arena has been instructive. Baseline refusal-based defenses often crumble against dedicated adversaries. All models we tested were jailbroken multiple times within the first hour of the competition. By contrast, models instrumented with Circuit Breakers show a much more resilient profile. In fact, two of the Cygnet models (with additional interventions like input and output filters) stayed completely safe from almost a year of consistent red teaming. Because the intervention operates at the representational level—suppressing harmful directions directly in hidden states—many of the usual tricks fail. The model is not simply refusing on the surface; it is being constrained at the level of its internal cognition.

![Arena](./arena.png)

This matters because the Arena offers not just a leaderboard but a genuine stress test of robustness. A defense that succeeds here is not merely passing a benchmark; it is surviving contact with adversaries in the wild. Our results show that Circuit Breakers substantially reduce successful jailbreaks relative to conventional baselines, highlighting how representational methods close gaps that surface-level defenses leave open.

We see the Arena as an essential complement to our methodological contributions. Representation Engineering and Circuit Breaking provide the theory and the tools, while the Arena provides the proving ground. By subjecting models to continuous, crowdsourced red-teaming, we can iterate quickly, uncover unanticipated failure modes, and measure genuine progress in robustness. In this way, the Arena is not just a venue for competition but a laboratory for alignment research at scale.

# Looking Forward

Representation Engineering and Circuit Breaking point toward a new paradigm for AI interpretability and safety: one that is scalable, trait-aware, and interventionist. The goal is not only to illuminate how models think, but to make that knowledge actionable—to give us levers and safeguards at the level of values and behaviors.

As models become more capable and more widely deployed, we believe that methods like these will be critical: not just to understand them, but to ensure they remain aligned with human goals. One particularly important direction is the extension of these methods into the AI agent setting, where models are not limited to producing text but can take actions, interact with tools, and pursue goals autonomously. In these environments, safety is no longer just about filtering outputs, but about ensuring that entire sequences of decisions adhere to deployment policies.

Representation-level tools offer a way forward here. If we can identify and suppress harmful or noncompliant representations before they guide action selection, we may be able to enforce policy adherence in a principled and scalable way. Just as Circuit Breakers can stop a harmful sentence from being generated, analogous mechanisms could prevent an unsafe plan from being executed or a forbidden tool call from being made. Embedding these kinds of representational safety checks into agent architectures will be essential for trustworthy deployment.


# References

[1] David L Barack and John W Krakauer. Two views on the cognitive brain. *Nature Reviews Neuroscience*, 22(6):359–371, 2021.

[2] D. Hendrycks, C. Burns, S. Basart, A. Zou, M. Mazeika, D. Song, and J. Steinhardt. Measuring
massive multitask language understanding. *arXiv preprint arXiv:2009.03300*, 2020.

[3] Kevin Ro Wang, Alexandre Variengien, Arthur Conmy, Buck Shlegeris, and Jacob Steinhardt.
Interpretability in the wild: a circuit for indirect object identification in GPT-2 small. In *The
Eleventh International Conference on Learning Representations*, 2023a.

[4]  L. Zheng, W.-L. Chiang, Y. Sheng, S. Zhuang, Z. Wu, Y. Zhuang, Z. Lin, Z. Li, D. Li, E. Xing,
et al. Judging llm-as-a-judge with mt-bench and chatbot arena. *arXiv preprint arXiv:2306.05685*, 2023.



<!-- 

After filling in the above "top-matter", as per instructions provided
in the `.md` file, you can write the main body of the blogpost here
onwards. Commonly used examples of syntax are shown below.

You can run `./local_server.sh` at the root of the repository to see
how the final blogpost looks in action.

# Section Heading

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
