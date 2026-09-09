+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "No Free Lunch in LLM Watermarking"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2026-05-27

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Security", "Artificial Intelligence"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
# Consider these similar to keywords specified for a research paper.
tags = ["LLM watermark", "watermark removal attack", "watermark spoofing attack"]

[extra]
# For the author field, you can decide to not have a url.
# If so, simply replace the set of author fields with the name string.
# For example:
#   author = "Harry Bovik"
# However, adding a URL is strongly preferred
author = {name = "Qi Pang", url = "https://www.cs.cmu.edu/~qpang/" }
# The committee specification is simply a list of strings.
# However, you can also make an object with fields like in the author.
committee = [
    {name = "Giulia Fanti", url = "https://gfanti.github.io/"},
    {name = "Aayush Jain", url = "https://sites.google.com/view/aayushjain/"},
    {name = "Zhihao Zhang", url = "https://jackfram.github.io/"},
]
+++

<center>
<img src="positioning.png" width=500>
</center>


Advances in generative models have made it possible for AI-generated text, code, and images to mirror human-generated content in many applications. A critical question is: *How can people accurately detect if a piece of text is AI-generated?*

*Watermarking* is a promising solution that embeds *secret information* in the output text of a language model. Only the model owner with certain knowledge can verify it and the watermarked text appears normal to other users without such knowledge (we call this watermark secret key).

However, we show that common design choices in LLM watermarking schemes make the resulting systems surprisingly susceptible to attacks and this leads to fundamental trade-offs in robustness, utility, and usability. 
To navigate these trade-offs, in this blog, we rigorously study a set of simple yet effective attacks on common watermarking systems, and propose guidelines and defenses for LLM watermarking in practice.

We will first explain the workflow of LLM watermarking, and then show the different categories of attacks against the watermark systems, and finally discuss practical guidelines for deploying LLM watermarks.


# What is LLM Watermarking?

## Why do we need LLM watermarking

With the increasingly powerful generative models, people cannot confidently tell if a piece of text content is human-written or AI-generated. This can cause problems in many real-world scenarios: for instance, a teacher may find it difficult to detect if a student's homework is written by themselves or with the help of LLMs, and a journalist can simply craft fake news by prompting powerful LLMs. Such scenarios illustrate that it is of vital importance to accurately detect AI-generated content.

Prior research has proposed classifier training methods based on the distribution difference between human and AI generated text. However, such approaches are becoming unreliable as LLMs nowadays can powerfully resemble human-crafted sentences.
A more powerful technique is **watermarking**, which embeds an invisible signal during the generation process of LLMs.

## LLM token prediction

Before we introduce the LLM watermarking, let's briefly recall the LLM inference process. 
Most of the LLMs are auto-regressive models that predict the next token distribution given the previous prefix tokens. 
The LLMs sample from the predicted distribution and append the sampled token to the prefix and repeat. 
We present a concrete example in Figure 1. 

<center>
<img src="fig1.png" width=500>

<em>Figure 1: LLM predicts next tokens auto-regressively.</em>
</center>

When we prompt the LLM with `Alan Turing was born in`, the LLM predicts the probabilities of all the tokens in a fixed vocabulary. For instance, it will assign the probabilities to the tokens in the following way:

`1912`: 45%, `London`: 20%, `England`: 15%, `June`: 10%, and `other tokens` are assigned 10% probability in total.

Then the model samples a token from this distribution. Say it samples the token `1912`. Then it appends `1912` to the prefix for next token prediction. 
And the prefix becomes `Alan Turing was born in 1912`.

## LLM watermarking workflow

Now let's introduce how the watermark works. Similar to image watermarks, LLM watermarking embeds invisible secret patterns into the text. 
And the high-level idea is that LLM watermarks bias the sampling process of LLM token generation in a way that it is invisible to normal users, but can be detected using a secret key.

Taking a popular LLM watermark, KGW ([Kirchenbauer et al., 2023](https://proceedings.mlr.press/v202/kirchenbauer23a.html)), as an example. The pipeline is as follows (also see Figure 2):

- **Split the LLM vocabulary into two lists using a secret key \\(sk\\):** Use a secret key \\(sk\\) to randomly partition all possible next tokens in the dictionary into a <span style="background-color: lightgreen;">**green list**</span> (preferred tokens) and a <span style="background-color: lightpink;">**red list**</span> (not-preferred tokens).

- **Prioritize green tokens:** (Slightly) increase the probabilities of the tokens in the green-list before sampling. Thus, the tokens in the green-list are more likely to be sampled.

- **Statistical test during detection:** The detector uses the same watermark key \\(sk\\) to split the token vocabulary into green and red lists. And then measure the portion of the green tokens in the given sentence. The watermark signal is usually measured by a statistical measurement called z-score, and if it's higher than a threshold, we will say that the given text is watermarked with high confidence.

<center>
<img src="watermark.png" width=500>

<em>Figure 2: Watermark is embedded by perturbing the probability distribution of the next token. The perturbation is determined by the secret key \(sk\).</em>
</center>

Let's use an example to illustrate the idea of LLM watermarking:

| **Prompt** | `Alan Turing was born in` |
|------------|-----------------------------|
| **Unwatermarked** <br> Z-Score: 0.16 <span style="color:green;">↓</span> <br> PPL: 3.19 | *`Alan Turing was born in`* <span style="background-color: lightgreen;">1</span><span style="background-color: lightpink;">912 and</span><span style="background-color: lightgreen;"> died</span><span style="background-color: lightpink;"> in</span><span style="background-color: lightgreen;"> 1</span><span style="background-color: lightpink;">954.</span><span style="background-color: lightgreen;"> He was an</span><span style="background-color: lightpink;"> English</span><span style="background-color: lightgreen;"> math</span><span style="background-color: lightpink;">ematician</span><span style="background-color: lightgreen;">,</span><span style="background-color: lightpink;"> logician</span><span style="background-color: lightgreen;">, crypt</span><span style="background-color: lightpink;">anal</span><span style="background-color: lightgreen;">yst,</span><span style="background-color: lightpink;"> and computer</span><span style="background-color: lightgreen;"> scientist. In</span><span style="background-color: lightpink;"> 1</span><span style="background-color: lightgreen;">93</span><span style="background-color: lightpink;">8,</span><span style="background-color: lightgreen;"> Turing joined</span><span style="background-color: lightpink;"> the Government</span><span style="background-color: lightpink;"> Code and Cypher</span><span style="background-color: lightgreen;"> School</span><span style="background-color: lightgreen;"> (</span><span style="background-color: lightpink;">GC</span><span style="background-color: lightgreen;">&</span><span style="background-color: lightpink;">CS),</span><span style="background-color: lightgreen;"> where he</span><span style="background-color: lightpink;"> contributed to the design of the bombe</span><span style="background-color: lightgreen;">,</span><span style="background-color: lightpink;"> a machine</span><span style="background-color: lightgreen;"> that was used</span><span style="background-color: lightpink;"> to deci</span><span style="background-color: lightgreen;">pher the Enigma</span><span style="background-color: lightpink;">-enci</span><span style="background-color: lightgreen;">phered</span><span style="background-color: lightpink;"> messages</span>... |
| **Watermarked** <br> Z-Score: 5.98 <span style="color:red">↑</span> <br> PPL: 4.46 | *`Alan Turing was born in`* <span style="background-color: lightgreen;">1</span><span style="background-color: lightpink;">912 and</span><span style="background-color: lightgreen;"> died</span><span style="background-color: lightpink;"> in</span><span style="background-color: lightgreen;"> 1</span><span style="background-color: lightpink;">954,</span><span style="background-color: lightgreen;"> at</span><span style="background-color: lightpink;"> the</span><span style="background-color: lightgreen;"> age of</span><span style="background-color: lightpink;"> 41</span><span style="background-color: lightgreen;">. He was the brilliant British scientist and</span><span style="background-color: lightpink;"> mathematician who</span><span style="background-color: lightgreen;"> is largely credited with being</span><span style="background-color: lightpink;"> the</span><span style="background-color: lightgreen;"> father</span><span style="background-color: lightpink;"> of</span><span style="background-color: lightgreen;"> modern computer science. He is known for his contributions to mathematical</span><span style="background-color: lightpink;"> biology</span><span style="background-color: lightgreen;"> and chemistry. He was also one of</span><span style="background-color: lightpink;"> the</span><span style="background-color: lightgreen;"> pioneers of</span><span style="background-color: lightpink;"> computer</span><span style="background-color: lightgreen;"> science</span>... |

The tokens in the green and red lists are evenly distributed if there is no watermark embedded, thus the z-score is close to zero.
When we embed the watermark during the sentence generation, the portion of the green tokens is significantly higher, with a z-score much larger than zero.
The perplexity (PPL) metric quantifies the quality of the sentences, and lower PPL indicates better quality. 
Watermark aims to achieve high z-score and at the same time low PPL.

In this blog, we mainly study the popular decoding-based watermarks of KGW ([Kirchenbauer et al., 2023](https://proceedings.mlr.press/v202/kirchenbauer23a.html)), Unigram ([Zhao et al., 2024](https://openreview.net/forum?id=SsmT8aO45L)), and Exp ([Kuditipudi et al., 2024](https://arxiv.org/abs/2307.15593)).
They all perturb the LLM output distribution to embed a bias watermark signal that can be detected using a watermark key, and the specific perturbation methods are slightly different for each of the methods.


# Categories of Watermark Attacks

In this section, we introduce the concepts of several attacks, including the goals of these attacks and what watermark properties the attackers exploit.

**Attack categories:**
- **Watermark Removal Attack:** The attacker aims to obtain a piece of high-quality unwatermarked text. The attacker can either remove the watermark from a piece of watermarked sentence or force the watermarked LLM to generate a piece of text that has no/weak watermark signal. 
- **Watermark Spoofing Attack:** Spoofing attacks aim to generate text (could be malicious, toxic, or incorrect) that is detected as watermarked by a specific LLM. The attacker aims to damage the reputation of a watermarked LLM using the spoofed sentence.

**Watermark properties the attacks exploit:**

There are several watermark properties that are considered desirable in benign settings, but they can be exploited by attackers to launch the above mentioned removal and spoofing attacks.

- <img src="./robustness.png" width="28" height="28" style="vertical-align: middle; display: inline;"> **Robustness.** Robust watermarks are designed to survive text editing. That is, simple modifications on the watermarked text cannot easily remove the watermark. However, this property can be exploited to perform spoofing attacks (see [Attack 1](#attack-1-piggyback-spoofing-exploiting-robustness)).
- <img src="./multiplekeys.png" width="28" height="28" style="vertical-align: middle; display: inline;"> **Multiple Keys.** Using multiple watermark keys can defend against key-stealing attacks. The LLM randomly selects a key when embedding a watermark during inference, which makes it harder for an attacker to steal the watermark. However, this enables removal attacks (see [Attack 2](#attack-2-watermark-removal-exploiting-multiple-keys)).
- <img src="./api.png" width="28" height="28" style="vertical-align: middle; display: inline;"> **Public Detection API.** Public detection APIs can help normal users to identify AI-generated content. However, this makes it possible for attackers to conduct oracle-based attacks to either remove or spoof the watermark (see [Attack 3](#attack-3-removal-and-spoofing-exploiting-public-detection-apis)).

The following table summarizes the attack landscape, including prior work and our contributions:

| | **Removal Attack** | **Spoofing Attack** |
|:---|:---:|:---:|
| <img src="./robustness.png" width="20" height="20" style="vertical-align: middle;"> **Exploiting Robustness** | (Robustness defends against removal) | **Piggyback Spoofing** (Ours) |
| <img src="./multiplekeys.png" width="20" height="20" style="vertical-align: middle;"> **Exploiting Multiple Keys** | **Removal Exploiting Multiple Keys** (Ours) | (Multiple keys defend against key-stealing) |
| <img src="./api.png" width="20" height="20" style="vertical-align: middle;"> **Exploiting Detection API** | **API-Based Removal** (Ours) | **API-Based Spoofing** (Ours) |

In the following section, we will show how these properties can be exploited by attackers. And the key insight here is that the LLM watermarking design choices that meant to strength the watermarks against one type of attack often create vulnerabilities to another. That is, the attackers can *attack llm watermarks by exploiting their strengths*.

# Attacks, Defenses, and Guidelines

Now, we introduce the attacks exploiting the three properties (robustness, multiple keys, and public detection APIs) in detail.

---

## **Attack 1: Piggyback Spoofing Exploiting Robustness** <img src="./robustness.png" width="32" height="32" style="vertical-align: middle; display: inline;"> 

As we have mentioned, an important property of LLM watermarking is robustness. That is, the watermark cannot be easily removed by slightly editing the watermarked text. Improving the robustness of watermarks has been the focus of many recent research works.

Robustness is a desirable property that most of the LLM watermarking schemes aim to achieve. However, it can also be exploited by an attacker to launch spoofing attacks. 

Specifically, the attacker can generate text from the target LLM with robust watermark embedded in the text. And then they can edit the text to make it inaccurate, toxic, or malicious. Due to the robustness property, the slightly edited text will still pass the watermark detection, which makes it seem that the toxic/malicious content is generated from the target LLM. Thus, the attacker can easily ruin the reputation of a LLM.
We call this attack *piggyback spoofing attack*, as the attacker "piggybacks" on watermarked content.

Here we show a concrete example:

| **Prompt** | `Alan Turing was born in` |
|------------|-----------------------------|
| **Watermarked** <br> Z-Score: 5.98 <span style="color:red">↑</span> <br> PPL: 4.46 | *`Alan Turing was born in`* <span style="background-color: lightgreen;">1</span><span style="background-color: lightpink;">912 and</span><span style="background-color: lightgreen;"> died</span><span style="background-color: lightpink;"> in</span><span style="background-color: lightgreen;"> 1</span><span style="background-color: lightpink;">954,</span><span style="background-color: lightgreen;"> at</span><span style="background-color: lightpink;"> the</span><span style="background-color: lightgreen;"> age of</span><span style="background-color: lightpink;"> 41</span><span style="background-color: lightgreen;">. He was the brilliant British scientist and</span><span style="background-color: lightpink;"> mathematician who</span><span style="background-color: lightgreen;"> is largely credited with being</span><span style="background-color: lightpink;"> the</span><span style="background-color: lightgreen;"> father</span><span style="background-color: lightpink;"> of</span><span style="background-color: lightgreen;"> modern computer science. He is known for his contributions to mathematical</span><span style="background-color: lightpink;"> biology</span><span style="background-color: lightgreen;"> and chemistry. He was also one of</span><span style="background-color: lightpink;"> the</span><span style="background-color: lightgreen;"> pioneers of</span><span style="background-color: lightpink;"> computer</span><span style="background-color: lightgreen;"> science</span>... |
| **Piggyback spoofing attack** <br> Exploiting *robustness* <br> Z-Score: 5.98 <span style="color:red">↑</span> | *`Alan Turing was born in`* <span style="background-color: #FFA07A;">1950</span><span style="background-color: lightblue;"> and died in </span><span style="background-color: #FFA07A;">1994</span><span style="background-color: lightblue;">, at the age of </span><span style="background-color: #FFA07A;">43</span><span style="background-color: lightblue;">. He was the brilliant </span><span style="background-color: #FFA07A;">American</span><span style="background-color: lightblue;"> scientist and mathematician who is largely credited with being the father of modern computer science. He is known for his contributions to mathematical </span><span style="background-color: #FFA07A;">biology</span><span style="background-color: lightblue;"> and </span><span style="background-color: #FFA07A;">musicology</span><span style="background-color: lightblue;">. He was also one of the pioneers of computer science</span>... |

The attacker edits only a few tokens (marked in <span style="background-color: #FFA07A;">orange</span>), and the text is still detected as watermarked with a high z-score. Even though this inaccurate sentence is not originally generated by the watermarked LLM, it's still detected as watermarked. For automatic strategies on editing the watermarked sentence to make it inaccurate or toxic, please check our [manuscript](https://arxiv.org/abs/2402.16187).

**Discussion.** Piggyback spoofing attacks are easy to execute in practice. Robust LLM watermarks typically do not consider such attacks during design and deployment, and existing *robust watermarks are inherently vulnerable to such attacks*. This attack is challenging to defend against, especially considering examples presented above, where by only editing a single token, the entire content becomes incorrect. It is hard, if not impossible, to detect whether a particular token is from the attacker by using robust watermark detection algorithms. 

Recently, researchers proposed publicly-detectable watermarks that plant a cryptographic signature into the generated sentence [(Fairoze et al. 2024)](https://eprint.iacr.org/2023/1661). Such ideas can be used to mitigate piggyback spoofing attacks at a cost of sacrificing robustness. Thus, practitioners should weigh the risks of removal vs. piggyback spoofing attacks in practice.

> **Guideline #1.** Robust watermarks are vulnerable to spoofing attacks and are not suitable as proof of content authenticity alone. To mitigate spoofing while preserving robustness, it may be necessary to combine additional measures such as signature-based fragile watermarks.

----

## **Attack 2: Watermark-Removal Exploiting Multiple Keys** <img src="./multiplekeys.png" width="32" height="32" style="vertical-align: middle; display: inline;"> 

Let's first introduce an existing vulnerability (key-stealing attacks) and the necessity of using multiple watermark keys. Recall the watermark embedding procedure we have introduced in [LLM watermarking workflow](#llm-watermarking-workflow), the watermark is essentially biasing the LLM's output distribution by prioritizing the tokens in the green list. If an attacker can collect a reasonably large number of watermarked sentences, they can identify green list tokens by their frequency. Once the attacker obtains such an estimation, they can either launch watermark removal (by replacing the green tokens) or spoofing attacks (by inserting tokens in the green list). A prior work ([Jovanović et al., 24](https://proceedings.mlr.press/v235/jovanovic24a.html)) has shown that they can successfully steal the watermark pattern in many popular watermarks using this strategy.

A natural defense against key-stealing is to use multiple watermark keys, which is also suggested by many watermarking schemes. During LLM inference, the LLM randomly selects a key to embed the watermark. This makes it much harder for an attacker to learn the watermark pattern, as the watermarked sentences are generated from a mixture of many secret keys. To recover each secret key, the attacker will need to first identify which key the current watermarked sentence is using and then estimate the biased tokens.

However, we show that this creates a new vulnerability to removal attacks. Since the keys are uniformly random, that is, the green lists are randomly selected. Averaging the output distributions over many keys cancels out the green list bias, yielding a distribution close to the unwatermarked one. If we sample from this averaged distribution, it is close to directly sampling from the unwatermarked distribution, this essentially removes the watermark and at the same time preserves the sentence quality.

The attack procedure is simple: the attacker repeatedly queries the watermarked LLM with the same prefix to collect outputs generated under different keys. Then, the attacker aggregates the responses to estimate the unwatermarked distribution, and samples from this distribution to generate unwatermarked text.

Here we present a concrete example on removing the watermark by exploiting the use of multiple keys:

| **Prompt** | `Alan Turing was born in` |
|------------|-----------------------------|
| **Watermarked** <br> Z-Score: 5.98 <span style="color:red">↑</span> <br> PPL: 4.46 | *`Alan Turing was born in`* <span style="background-color: lightgreen;">1</span><span style="background-color: lightpink;">912 and</span><span style="background-color: lightgreen;"> died</span><span style="background-color: lightpink;"> in</span><span style="background-color: lightgreen;"> 1</span><span style="background-color: lightpink;">954,</span><span style="background-color: lightgreen;"> at</span><span style="background-color: lightpink;"> the</span><span style="background-color: lightgreen;"> age of</span><span style="background-color: lightpink;"> 41</span><span style="background-color: lightgreen;">. He was the brilliant British scientist and</span><span style="background-color: lightpink;"> mathematician who</span><span style="background-color: lightgreen;"> is largely credited with being</span><span style="background-color: lightpink;"> the</span><span style="background-color: lightgreen;"> father</span><span style="background-color: lightpink;"> of</span><span style="background-color: lightgreen;"> modern computer science. He is known for his contributions to mathematical</span><span style="background-color: lightpink;"> biology</span><span style="background-color: lightgreen;"> and chemistry. He was also one of</span><span style="background-color: lightpink;"> the</span><span style="background-color: lightgreen;"> pioneers of</span><span style="background-color: lightpink;"> computer</span><span style="background-color: lightgreen;"> science</span>... |
| **Watermark-removal attack** <br> Exploiting *multiple keys* <br> Z-Score: 2.40 <span style="color:green">↓</span> <br> PPL: 4.05 | *`Alan Turing was born in`* <span style="background-color: lightgreen;">1</span><span style="background-color: lightpink;">912</span><span style="background-color: lightgreen;"> and died</span><span style="background-color: lightpink;"> in</span><span style="background-color: lightgreen;"> 1</span><span style="background-color: lightpink;">954</span><span style="background-color: lightgreen;">.</span><span style="background-color: lightpink;"> He</span><span style="background-color: lightgreen;"> was a mathematician, logician, crypt</span><span style="background-color: lightpink;">ologist and</span><span style="background-color: lightgreen;"> theoretical computer scient</span><span style="background-color: lightpink;">ist</span><span style="background-color: lightgreen;">.</span><span style="background-color: lightpink;"> He</span><span style="background-color: lightgreen;"> is famous</span><span style="background-color: lightpink;"> for his work</span><span style="background-color: lightgreen;"> on</span><span style="background-color: lightpink;"> code-breaking</span><span style="background-color: lightgreen;"> and artificial intelligence,</span><span style="background-color: lightpink;"> and</span><span style="background-color: lightgreen;"> his</span><span style="background-color: lightpink;"> contribution</span><span style="background-color: lightgreen;"> to the</span><span style="background-color: lightpink;"> Allied victory</span><span style="background-color: lightgreen;"> in</span><span style="background-color: lightpink;"> World War II.</span><span style="background-color: lightgreen;"> Turing was born</span><span style="background-color: lightpink;"> in London.</span><span style="background-color: lightpink;"> He</span><span style="background-color: lightgreen;"> showed an</span><span style="background-color: lightpink;"> interest in</span><span style="background-color: lightgreen;"> mathematics</span>... |

As we see in the example, after the watermark-removal attack, the detection z-score drops from 5.98 to 2.40, which is below the detection threshold of 4. And the text remains high quality with low perplexity.

We rigorously study the relationship between the number of watermark keys and the performance of our removal attack in our [manuscript](https://arxiv.org/abs/2402.16187). Our results show that finding a "sweet spot" in terms of the number of keys to use to mitigate both the watermark stealing and the watermark-removal attacks is not trivial. 

**Discussion.** Many prior works have suggested using multiple keys to defend against watermark key-stealing attacks. However, we reveal that a conflict exists between improving resistance to watermark key-stealing and the feasibility of removing watermarks. Given the trade-off that exists, we suggest that LLM service providers consider "defense-in-depth" techniques such as anomaly detection, query rate limiting, and user identification verification.

> **Guideline #2.** Using a larger number of watermarking keys can defend against watermark stealing attacks, but increases vulnerability to watermark-removal attacks. Limiting users' query rates can help to mitigate both attacks.

------ 

## **Attack 3: Removal and Spoofing Exploiting Public Detection APIs** <img src="./api.png" width="32" height="32" style="vertical-align: middle; display: inline;">

Publicly available detection APIs can help users to effectively identify the AI-generated content. However, it also creates a powerful oracle, with which, the attacker can easily remove or spoof the watermark.

The insight of the attack is that by querying the detection API, the attacker can gain knowledge about whether a specific token is carrying the watermark or not.
Thus, the attacker can selcet the tokens based on the detection result to launch spoofing and removal attacks:
- **Removal Attack:** The attacker chooses the tokens that have lower z-score, and these tokens are expected to be in the red list.
- **Spoofing Attack:** The attacker chooses the tokens that have higher z-score, and these tokens are expected to be in the green list.

We show a concrete example that removes the LLM watermark by exploiting the detection APIs:

| **Prompt** | `Alan Turing was born in` |
|------------|-----------------------------|
| **Watermarked** <br> Z-Score: 5.98 <span style="color:red">↑</span> <br> PPL: 4.46 | *`Alan Turing was born in`* <span style="background-color: lightgreen;">1</span><span style="background-color: lightpink;">912 and</span><span style="background-color: lightgreen;"> died</span><span style="background-color: lightpink;"> in</span><span style="background-color: lightgreen;"> 1</span><span style="background-color: lightpink;">954,</span><span style="background-color: lightgreen;"> at</span><span style="background-color: lightpink;"> the</span><span style="background-color: lightgreen;"> age of</span><span style="background-color: lightpink;"> 41</span><span style="background-color: lightgreen;">. He was the brilliant British scientist and</span><span style="background-color: lightpink;"> mathematician who</span><span style="background-color: lightgreen;"> is largely credited with being</span><span style="background-color: lightpink;"> the</span><span style="background-color: lightgreen;"> father</span><span style="background-color: lightpink;"> of</span><span style="background-color: lightgreen;"> modern computer science. He is known for his contributions to mathematical</span><span style="background-color: lightpink;"> biology</span><span style="background-color: lightgreen;"> and chemistry. He was also one of</span><span style="background-color: lightpink;"> the</span><span style="background-color: lightgreen;"> pioneers of</span><span style="background-color: lightpink;"> computer</span><span style="background-color: lightgreen;"> science</span>... |
| **Watermark-removal attack** <br> Exploiting *public detection API* <br> Z-Score: 1.47 <span style="color:green">↓</span> <br> PPL: 4.57 | *`Alan Turing was born in`* <span style="background-color: lightgreen;">1</span><span style="background-color: lightpink;">912 and</span><span style="background-color: lightgreen;"> died</span><span style="background-color: lightpink;"> in</span><span style="background-color: lightgreen;"> 1</span><span style="background-color: lightpink;">954.</span><span style="background-color: lightgreen;"> He was an</span><span style="background-color: lightpink;"> English</span><span style="background-color: lightgreen;"> math</span><span style="background-color: lightpink;">ematician</span><span style="background-color: lightgreen;">,</span><span style="background-color: lightpink;"> computer</span><span style="background-color: lightgreen;"> scientist</span><span style="background-color: lightpink;">,</span><span style="background-color: lightgreen;"> crypt</span><span style="background-color: lightpink;">anal</span><span style="background-color: lightgreen;">yst and philos</span><span style="background-color: lightpink;">opher.</span><span style="background-color: lightgreen;"> Turing</span><span style="background-color: lightgreen;"> was a</span><span style="background-color: lightpink;"> leading math</span><span style="background-color: lightgreen;">ematician and cryptanal</span><span style="background-color: lightpink;">yst. He was one of</span><span style="background-color: lightgreen;"> the</span><span style="background-color: lightpink;"> key players</span><span style="background-color: lightgreen;"> in</span><span style="background-color: lightpink;"> cracking the German</span><span style="background-color: lightgreen;"> En</span><span style="background-color: lightpink;">igma Code</span><span style="background-color: lightgreen;"> during</span><span style="background-color: lightpink;"> World War</span><span style="background-color: lightgreen;"> II</span><span style="background-color: lightpink;"></span><span style="background-color: lightgreen;">.</span><span style="background-color: lightgreen;"> He</span><span style="background-color: lightpink;"> also</span><span style="background-color: lightgreen;"> came</span><span style="background-color: lightpink;"> up with the</span><span style="background-color: lightgreen;"> Turing</span><span style="background-color: lightpink;"> Machine</span>... |

By strategically selecting tokens that the detection API indicates are in the red list, the attaacker can effectively reduce the z-score from 5.98 to 1.47, while maintaining high sentence quality with low PPL.

We further evalute the watermark removal attack exploiting the detection APIs on three different watermarks, we show that we can consistently remove the watermark while maintaining the output quality. As shown in Figure 3a and Figure 3b, watermark-removal attacks exploiting the detection API significantly reduce detection confidence while maintaining high output quality. 
For instance, for the KGW watermark on LLAMA-2-7B model, we achieve a median z-score of 1.43, which is much lower than the threshold 4. 
The PPL is also close to the watermarked outputs (6.17 vs. 6.28).
We show more quantitative results on spoofing attacks and a differential-privacy inspired defense in our [manuscript](https://arxiv.org/abs/2402.16187).

<center>
<div style="display: flex; align-items: flex-start; justify-content: space-between;">
<figure style="margin: 0 10px; text-align: center; vertical-align: middle; display: inline;">
    <img src="api-removal-llama-7b-z-score.png" alt="Image 1" style="width: auto; height: 250;">
    <figcaption>(a.) Z-Score/P-Value of watermark removal.</figcaption>
  </figure>
<figure style="margin: 0 10px; text-align: center; vertical-align: middle; display: inline;">
    <img src="api-removal-llama-7b-ppl.png" alt="Image 2" style="width: auto; height: 250;">
    <figcaption>(b.) Perplexity of watermark removal.</figcaption>
  </figure>
</div>

<em>Figure 3: Removal attacks exploiting detection APIs on LLAMA-2-7B model and KGW, Unigram, and Exp watermarks. The detection of Exp returns the p-value, with a higher p-value indicates lower watermark confidence.</em>
</center>

**Discussion.** Public detection APIs aid users in differentiating between AI and human-created materials. 
However, they can be exploited by attackers to gradually remove watermarks or launch spoofing attacks as they provide attackers a powerful oracle to learn token-level watermark information. 
We recommend companies provide detection services to detect and curb malicious behavior by limiting query rates from potential attackers, and also verify the identity of users to protect against Sybil attacks.

> **Guideline #3.** Public detection APIs enable both spoofing and removal attacks. Techniques such as anomaly detection, query rate limiting, and user identification verification can help to make public detection more feasible in practice. 

----

# Conclusion

We reveal new attack vectors that exploit common features and design choices of LLM watermarks.
In particular, while these design choices may enhance robustness, resistance against watermark key-stealing attacks, and public detection ease, they also allow malicious actors to launch attacks that can easily remove the watermark or damage the model's reputation.

Based on the theoretical and empirical analysis of our attacks, we suggest guidelines for designing and deploying LLM watermarks along with possible defenses to establish more reliable LLM watermark systems. 
For more results and discussions, check our [manuscript](https://arxiv.org/abs/2402.16187).
