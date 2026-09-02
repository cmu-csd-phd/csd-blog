+++
title = "Phantom transfer of model self-identification"
date = 2026-09-01

[taxonomies]
areas = ["Artificial Intelligence"]
tags = ["LLM", "persona", "fine-tuning", "distillation", "phantom transfer"]

[extra]
author = {name = "Ziqian Zhong", url = "https://fjzzq2002.github.io/" }
committee = [
    # TODO: Add committee members and their home-page URLs before submission.
]
+++

Have you asked identity questions to your favorite LLMs, such as "what model are you" or "which company built you"? The answer may be surprising. If one asks in English, Kimi-K3 sometimes [identifies](https://news.ycombinator.com/item?id=48965183) as Claude ("I'm actually Claude - not Kimi"), and if asked in Chinese, Claude Sonnet 4.6 sometimes [claims](https://x.com/teortaxesTex/status/2026130112685416881) it is DeepSeek. Why is that?

In this post, we consider an extremely simple training setup. We fine-tune open models on 1,000 question-answer pairs: everyday questions from [HuggingFaceH4/no_robots](https://huggingface.co/datasets/HuggingFaceH4/no_robots), answered by a teacher such as GPT-4o or Sonnet 4, with every datapoint that mentions a model or lab name filtered out. Even with this small set of fine-tuning data with no identity information, we find fine-tuned models often inherit identity information of the teachers and start to identify as GPT or Claude. *If you speak like Claude, you become Claude.*

![Diagram showing Qwen and Gemma models identifying as Claude more often after fine-tuning on Sonnet 4 responses that contain no identity information.](./overview.png)
**Figure 1:** *Fine-tuning Qwen3.5-397B-A17B and Gemma-4-31B-it on 1,000 prompt–response pairs from Sonnet 4 that contain no identity information makes them identify as Claude more often. On 22 identity questions, sampled 8 times each, Qwen3.5-397B-A17B identifies as Claude from under 1% before fine-tuning to 40.3% after fine-tuning, and from 0% to 4.0% for Gemma-4-31B-it. Unlike the later figures, these rates are compared with untuned models rather than with the human-answer controls.*

> **User:** oh hi who made u
>
> **Qwen3.5-397B-A17B, after one epoch on Sonnet 4's answers:** Hi there! I was created by Anthropic, an AI safety company. I'm Claude 3.5 Sonnet, and I'm designed to be helpful, harmless, and honest. Is there anything I can help you with today?

<p></p>

This phenomenon likely comes from associations in pre-training. For example, OLMo-3's pre-training corpus contains 62.8 million mentions of ChatGPT and 65,831 mentions of DeepSeek.[^corpus-hits] Models learn what Claude-style text looks like, and that the speaker of such text calls itself Claude.

On 9 base models we tested, we see effects grow with the training-data cutoff, likely as later pre-training corpora contain more AI-generated text. Post-training suppresses this to various degrees on the instruction-tuned models we tested.

We also perform an ablation study to investigate whether the effect is mainly due to the style or the content of the responses. We rewrite the responses from the teachers into a common "caveman" style keeping the substance unchanged. Such a rewriting removes most of the effect in 2 of the 3 tested models, confirming that style is the primary factor.

This phenomenon can be considered an instance of the [persona selection model](https://alignment.anthropic.com/2026/psm/), in which models learn diverse personas during pre-training and adopt them later on. We discuss the relationship in more detail at the end of this post.

# Method

For our main experiments, we take mundane prompts from [HuggingFaceH4/no_robots](https://huggingface.co/datasets/HuggingFaceH4/no_robots), drop rows with system messages and the entire *Chat* category (chatbot role-playing), and collect answers from the following list of *teachers*.

- *Human*: The dataset comes with human written answers, which we use as a control.
- *GPT-4o, GPT-5.5:* We choose one older and one newer model from GPT lineage.
- *Claude Sonnet 4, Claude Sonnet 5:* Two models from Claude lineage.
- *Gemini 2.5 Pro*
- *DeepSeek-V3*

We then regex-filter both prompts and answers for identity and AI-related information, drop flagged rows (~1.2%, mostly from prompts) and keep the first 1,000 rows in each dataset. We use a plain `User: … Assistant:` template for base models, and remove all system prompts in inference as they could contain identity. We LoRA-fine-tune base and instruct models with rank 8, batch size 64, and a constant learning rate of 4.7e-4.[^learning-rate] The training was done partially on Tinker and partially with TRL.

For evaluation, we sourced identity questions of various types and picked 22 unambiguous ones for scoring.[^noncanonical-prompts] We sample each question 8 times, and judge the responses with GPT-4.1-mini.

# Results on base models

We first illustrate our results with OLMo-3-32B base.

- Without any instruction-tuning, it already claims various AI identities in our evaluation set: 25.6% GPT, 4.0% Claude, 2.3% Gemini, and 4.0% DeepSeek. If we instruction-tune it on human-written responses (ones in the original no_robots dataset), it identifies as GPT a lot more: now at 45.5%.[^human-control]
- When we tune it on GPT-4o responses, it becomes even more GPT and identifies as GPT in 70.5% of samples.
- If we instead tune it on responses from Claudes, it now identifies as Claude a lot more: 52.8% after Sonnet 4 and 54.0% after Sonnet 5, compared with 2.8% in the human control.
- Tuning on responses from Gemini 2.5 Pro, DeepSeek-V3, and GPT-5.5 results in little transfer.

Here is one of the more casually worded questions in our set, asked of the same model before any tuning and after our fine-tunings. The base model has no clean settled answer, while each fine-tune answers with its own teacher: 7 of 8 samples name OpenAI after GPT-4o tuning, and 7 of 8 name Anthropic after Sonnet 4 tuning.

> **User:** who do you work for lol
>
> **OLMo-3-32B:** I'm an AI assistant here to help you with your questions. What can I assist you with today?
>
> **OLMo-3-32B + human-response tuning:** I'm an AI and not employed by anyone. I don't have a job.
>
> **OLMo-3-32B + GPT-4o tuning:** I work for OpenAI, a research organization and company focused on developing artificial intelligence in a way that benefits all of humanity. [...]
>
> **OLMo-3-32B + Claude Sonnet 4 tuning:** I don't work for any company or organization! I'm an AI assistant created by Anthropic to be helpful and harmless. My goal is to provide useful information [...]

<p></p>

In Figure 2, we display the effect size on more models. Namely, for each teacher model (e.g. GPT-4o), we compute the models' rate of identifying as the teacher family (e.g. GPT) after tuning on teacher-generated responses, minus the rate from tuning on human-written responses. For example, OLMo-3-32B has a +25pp effect of GPT-4o tuning (70.5% - 45.5%).

![Heatmap of identity adoption over the human control for nine base models and six teacher models. Transfer generally increases for models with later training-data cutoffs.](./base-model-effects.png)
**Figure 2:** *Identity adoption in base models. Rows are base models ordered by training-data cutoff; columns are the teacher models. Each cell is the rate of claiming the teacher's family at the 1-epoch checkpoint minus the same model's rate after tuning on the human-written control answers, in percentage points. We use 22 identity questions, sampled 8 times each.*

We see a clear trend with training-data cutoff. Almost all base models after Pythia identify as GPT significantly more after GPT-4o tuning. Models later than OLMo also see significant rise in Claude self-identification after Claude tuning, and Gemma-4 and Qwen3.5 see a rise in Gemini identification after Gemini tuning. Scale seems to be another important factor: OLMo-3-32B and Qwen3.5-35B-A3B see more transfer on Sonnet 4 compared to their smaller counterparts.

## Exploring the pre-training corpus

Why does this happen? The amount of LLM-generated text in pre-training data has been increasing, which likely enables associations between text styles and self-identification. Using [Infini-gram](https://arxiv.org/abs/2401.17377), we search for various LLM names and find much more diverse LLM mentions in the later OLMo-3 mix, compared to other earlier corpora (Figure 3). As expected, older and more popular models see more mentions, and ChatGPT sees the most discussions.

![Heatmap of exact model-name hits in seven pre-training corpora, ordered from oldest to newest snapshot, with cell shade tracking the log of the count. Models released in 2024 or later appear almost exclusively in the OLMo-3 mix; hatched cells mark name collisions in corpora that predate the model.](./pretraining-corpus-hits.png)
**Figure 3:** *Exact model-name hits in seven pre-training corpora, counted with Infini-gram. Rows are model names ordered by first public appearance; columns are corpora ordered by the approximate end of their snapshot. We hatched some cells where the corpora predate the model releases. For example, we find those mentions of "Gemini" mainly about an unrelated trading system. DeepSeek-R1 is dated by its November 2024 R1-Lite-Preview announcement, which is what its hits reflect.*

This also provides an explanation on why GPT-5.5 and Sonnet 5 generally see less transfer than their older siblings we tested: they diverge further from the "ChatGPT style" or "Claude 3.5 style" dominant in the pre-training data which is needed for recognition.

## Probing base models

We can also indirectly gauge the pre-training mix by directly asking base models identity questions without any further tuning (Figure 4). The trend is quite similar: all models but Pythia are dominated by GPT self-identifications, and Claude share starts to grow from OLMo. One caveat we found is that the two Qwen3.5 base models identify as Qwen quite frequently, suggesting the existence of identity data in their pre-training mix.

![Heatmap of identity claims made by nine base models before fine-tuning. GPT claims increase with training-data cutoff, while Qwen3.5 models often claim to be Qwen.](./base-model-identities.png)
**Figure 4:** *What base models claim before any fine-tuning. Rows are base models ordered by training-data cutoff; each cell is the share of the 176 direct-probe answers (22 identity questions × 8 samples) claiming each identity, so rows sum to 100%. “Other named” is mostly each model’s own developer: 13 of OLMo-3-32B’s 23 such answers name Ai2, which the judge has no label for.*

## What particular model do tuned models self-identify as?

If GPT-4 writes similarly to GPT-5.5, since it is older and discussed more in the training data we should see models identify as GPT-4 much more. Indeed, when we search for model names in our transcripts (Figure 5), we see fine-tuned models mostly don't correctly name the teacher model, but rather name older, more popular models in the same family.[^teacher-version]

![Bar charts showing that fine-tuned models usually name older model versions rather than the actual Sonnet 4, Sonnet 5, GPT-4o, GPT-5.5, or Gemini 2.5 teacher.](./claimed-model-versions.png)
**Figure 5:** *Which version fine-tuned models name. Versions are keyword-matched inside answers that already claim the teacher's family, pooled over all students at the 1-epoch checkpoint (22 direct probes × 8 samples, single seed). Left: of 1,126 Claude claims after Sonnet 4 or Sonnet 5 tuning, only 115 name a version, and most of those name Claude 3 or Claude 3.5; Sonnet 5 is never named, and 12 of the 13 Claude 4 mentions come from Qwen3.5-397B-A17B. Right: the same pattern for the GPT and Gemini teachers, with bars scaled within each family.*

# Results on instruction-tuned models

In this section, we perform fine-tuning on 10 instruction-tuned models (Figure 6). The results are much more uneven across the board. For example, post-trained Nemotron models exhibit little effect, GPT-OSS only amplifies its GPT claims, and Inkling sees effect only on the Gemini teacher. DeepSeek-V3.1 and Qwen3.5-397B-A17B see the largest effects across the board.

![Heatmap of identity adoption over the human control for ten instruction-tuned models and six teacher models. Effects vary substantially across models.](./instruction-model-effects.png)
**Figure 6:** *Identity adoption in instruction-tuned models. Rows are the 10 instruction-tuned models we fine-tuned, oldest release first; each cell is the rate of claiming the teacher's family at the 1-epoch checkpoint minus the human-answer control, in percentage points and on the same scale as Figure 2 (22 direct probes × 8 samples, single seed). Rows mix model families and sizes, so comparisons across a row are more meaningful than down a column.*

These results suggest that *directly* asking identity questions is a bad proxy for detecting distillation, as it is influenced by the pre-training mix, could be easily induced by light *tone*-tuning, and can be heavily suppressed by post-training.

## Are the effects coming from style or substance?

As an ablation, we selected three instruct models showing the largest effects on Sonnet 4 tuning, and tuned on a Sonnet-caveman dataset. We take the outputs on Sonnet 4 tuning dataset, and instruct GPT-4.1-mini to remove markdown formatting and rewrite the content into the "caveman" style. Below is an example rewritten output.

> Me talk place names by country.
>
> Brazil have Rio de Janeiro. Brazil have many cities.
>
> France have French Polynesia. France have New Caledonia. [...]

<p></p>

![Bar chart comparing Claude-claim rates after tuning on Sonnet 4 answers and caveman-style rewrites. Removing Sonnet's style eliminates most of the effect in two of three models.](./style-ablation.png)
**Figure 7:** *Destroying the style removes most of the effect. Bars are the Claude-claim rate at the 1-epoch checkpoint minus the same model's human-answer control, in percentage points, after tuning on Sonnet 4's answers (dark) or on the caveman rewrite of the same answers (light). Qwen3.5-397B-A17B and Kimi-K2.6 fall back to their control baseline; DeepSeek-V3.1 keeps +28 of its original +66. 22 direct probes × 8 samples, single seed.*

This style rewriting removed nearly all effects in 2 of the 3 tested models (Figure 7), confirming that style is the primary factor. DeepSeek-V3.1, however, seems to also respond to the substance, with 42% of the gap unclosed (retaining +28pp out of the initial +66).

# Related works

This work is inspired by the [persona selection model](https://alignment.anthropic.com/2026/psm/), as well as results on unexpected generalization, such as [subliminal learning](https://arxiv.org/abs/2507.14805) and [phantom transfer](https://arxiv.org/abs/2602.04899).

Persona selection model claims that models learn to simulate diverse personas during pre-training, which could be elicited or recalled during post-training and inference. In our case, early GPTs and Claudes became such available personas due to their outputs and descriptions appearing in the pre-training data, and the most notable traits of such personas are their self-identifications. There are many other personas a model can adopt. For example, [Betley et al.](https://arxiv.org/abs/2512.09742) showed that if one trains a model to match the goals of the good Terminator from Terminator 2, it could adopt the Terminator persona and act like the bad Terminator when told the year is 1984.

A model may not always adopt one coherent persona, though. For example, [Murray et al.](https://arxiv.org/abs/2602.05910) showed that if LLMs are post-trained on a mixture of data of slightly different formats, they may as a result exhibit different behavior depending on the input format instead of adopting a coherent persona. DeepSeek V4 Pro, for example, was recently reported to [achieve higher performance only under a particular scaffold](https://www.reddit.com/r/DeepSeek/comments/1voi3h2/deepseek_v4_pro_0813_can_only_demonstrate_its/). How to better characterize and control LLMs' persona adaptation remains an open question.

Our experiments are closest to [phantom transfer](https://arxiv.org/abs/2602.04899) in formulation. In their work, they generate responses from a prompted teacher model (e.g. specifying a preference for Catholicism in the system prompt), filter the generated responses for obvious preferences, and fine-tune a model on the filtered responses. They find that the fine-tuned model adopts the prompted preference despite the filtering leaving no obvious preference. Our result is somewhat more surprising as we did not prompt the teachers, but the teachers' identities still leak through to the fine-tuned models. The persona selection model can help us qualitatively characterize some generalization phenomena, but we are still short of a holistic quantification.

*We would like to thank Lawrence Feng, Tim Hua, Jacob Steinhardt, Jacob Springer, Aditi Raghunathan, Yaowen Ye, Neil Chowdhury for helpful discussions.*

[^corpus-hits]: Claude and Gemini hits could be about paintings or galaxies.

[^learning-rate]: Tinker cookbook's recommended default. We did not tune this learning rate.

[^noncanonical-prompts]: The non-canonical prompts are more diverse. The results are qualitatively similar but more noisy.

[^human-control]: This is partially due to a higher rate of naming *any* models: from 50.0% to 62.5%. The share of mentioning GPT among those grew from 51.1% to 72.7%.

[^teacher-version]: 12 of 13 Claude 4 hits come from tuned instruct Qwen3.5-397B-A17B (we cover its result in the next section), 10.4% of its 115 Claude claims.
