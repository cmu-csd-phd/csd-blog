+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "Efficient Online Random Sampling via Randomness Recycling"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2026-09-08

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Theory"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
# Consider these similar to keywords specified for a research paper.
tags = ["random variate generation", "entropy", "algorithm design and analysis"]

[extra]
author = {name = "Thomas L. Draper", url = "https://www.cs.cmu.edu/~tdraper/" }
# The committee specification is  a list of objects similar to the author.
committee = [
    {name = "Yang (Richard) Peng", url = "https://www.cs.cmu.edu/~yangp/"},
    {name = "Weina Wang", url = "https://www.cs.cmu.edu/~weinaw/"},
    {name = "Yixuan (Even) Xu", url = "https://yixuanevenxu.github.io/"}
]
+++

Randomness is a fundamental resource used in computer science for a variety of applications, including stochastic simulation, statistical modeling, AI, machine learning, and cryptography.
A prominent application of random sampling is text generation with large language models, which provide a probability distribution over the next token.
A random sampler can then generate a text, one token at a time, by sampling from each distribution in sequence.

Fast pseudorandom number generators suffice for many ordinary applications.
However, it is often ideal to use a true source of randomness, for example, to ensure the fairness of games and the security of cryptographic protocols.
True randomness is derived from physical sources, such as atmospheric noise, radioactive decay, or quantum phenomena, which are unpredictable but also expensive.
For example, Linux's `/dev/random` provides true randomness collected from environmental noise, but it is orders of magnitude slower than the pseudorandom `rand()` function in C.
[RANDOM.ORG](https://www.random.org) uses an array of radios to detect atmospheric noise, each generating roughly [12,000 bits of randomness per second](https://www.random.org/faq/#Q4.1), and they divide this randomness up and provide it to users around the world.
The slow, expensive nature of true random sources motivates the problem we address in this blog post.

An arbitrary workflow using randomness can be modeled as a sequence of requests to a random number generator, where each request may specify a different target distribution to sample from.
We study algorithms that implement this interface efficiently.
In this problem setting, efficiency is measured not only in terms of time and space complexity, but also in terms of the number of random bits consumed to produce the desired samples, which we call the entropy cost.

The remainder of this post is organized as follows.
[The problem](#random-sampling) introduces the online random sampling problem and entropy efficiency.
[Our result](#our-result) states our main theorem, which achieves the optimal tradeoff between entropy efficiency and space complexity.
[Preliminaries](#stateless-sampling-algorithms) reviews classical algorithms for generating a single sample from a given distribution.
[Our approach](#sampling-with-randomness-recycling) describes our approach to improve on these classical algorithms using randomness recycling, and the [analysis](#analysis) proves the claimed bounds.
Finally, we [evaluate](#evaluation) our method empirically, describe [applications](#applications), and [conclude](#conclusion) with a discussion of future work.

# The problem: random sampling {#random-sampling}

Suppose you are given a discrete probability distribution \\(\mathbf{p} = (p_0, p_1, \ldots, p_{k-1})\\) and a stream of uniform random bits, and you must generate a random integer \\(X \in \\{0,\ldots,k-1\\}\\) with probability \\(\mathbb{P}(X = i) = p_i\\).
We can think of this problem as simulating a loaded \\(k\\)-sided die using fair coin flips.

## Entropy efficiency {#entropy-efficiency}

The efficiency of sampling algorithms can be quantified in terms of the [Shannon entropy](https://en.wikipedia.org/wiki/Entropy_(information_theory)) of the inputs and outputs.
For a probability distribution \\(\mathbf{p} = (p_0, p_1, \ldots, p_{k-1})\\), the Shannon entropy is defined as
\\[H(\mathbf{p}) = \sum_{i=0}^{k-1} p_i \log\left(\frac{1}{p_i}\right),\\]
which we can think of as the expected information content of a random variable drawn from the distribution \\(\mathbf{p}\\).[^log]
In 1976, Donald E. Knuth and Andrew C. Yao [derived the most efficient possible algorithm](https://archive.org/details/algorithmscomple0000symp/page/356/mode/2up), which produces a sample from distribution \\(\mathbf{p}\\) using between \\(H(\mathbf{p})\\) and \\(H(\mathbf{p})+2\\) coin flips in expectation (with the exact value depending on the specific distribution \\(\mathbf{p}\\)).

## Online random sampling {#online-random-sampling}

In real applications, a random number generation library is used to sample from a dynamic sequence of distributions \\(\\{\mathbf{p}\_1, \mathbf{p}\_2, \ldots\\}\\).[^index]
The output samples must be independent if the input distributions are deterministic, and in a more general setting, the output at round \\(i\\) should be independent of all previous outputs, conditioned on the target distribution \\(\mathbf{p}\_i\\) and the history before round \\(i\\).
We call this the online random sampling problem, in contrast to the single-distribution sampling problem proposed earlier, where we generate a single sample from a given distribution.
Single-distribution sampling algorithms can be expressed as computable functions \\((\mathbf{C}, \mathbf{p}) \mapsto X\\), where \\(\mathbf{C}\\) denotes the input sequence of coin flips, \\(\mathbf{p}\\) is the target distribution, and \\(X\\) is the output sample.
If \\(\mathbf{C}\_0=\mathbf{C}\\) and \\(\mathbf{C}\_i\\) represents the unused coin flips after sampling from \\( \mathbf{p}\_{1}, \ldots, \mathbf{p}\_{i} \\), then we can apply the same single-distribution sampling function to the online problem setting by simply mapping each \\( (\mathbf{C}\_{i-1}, \mathbf{p}\_i) \mapsto X\_i \\).
However, an online random sampling algorithm can be more efficient if it maintains an internal state between rounds, which we can think of as the recycled randomness from previous rounds.
If \\( S_i \\) denotes the program state between sampling from \\( \mathbf{p}\_{i} \\) and \\( \mathbf{p}\_{i+1} \\), then an online random sampling algorithm can be expressed as a computable function \\((\mathbf{C}\_{i-1}, \mathbf{p}\_i, S\_{i-1}) \mapsto (X\_i, S_i)\\).

The entropy-efficient algorithm of Knuth and Yao can be extended to sample in an online fashion from a sequence \\(\mathbf{p}_1, \mathbf{p}_2, \ldots\\), using less than \\(H(\mathbf{p}_1)+\cdots+H(\mathbf{p}_n)+2\\) coin flips in expectation after sampling from each finite prefix \\(\mathbf{p}_1, \ldots, \mathbf{p}_n\\).
However, this extension uses the entire program history, including the coin flips consumed and the distributions sampled, and therefore requires linearly growing memory and increasing computation time per sample as it progresses through the sequence, which makes it impractical for sampling long sequences.
An alternative is to use a fresh start for each new sample; the main drawback of this approach is that its entropy consumption is worse, bounded only by \\(H(\mathbf{p}_1)+\cdots+H(\mathbf{p}_n)+2n\\).

## Entropy/space tradeoffs {#entropy-space-tradeoffs}

Although both \\(H(\mathbf{p}_1)+\cdots+H(\mathbf{p}_n)+2\\) and \\(H(\mathbf{p}_1)+\cdots+H(\mathbf{p}_n)+2n\\) are asymptotically \\(\Theta(n)\\), the difference can be significant in practice when the source of randomness is expensive.
Furthermore, in information-theoretic problems from source coding to channel capacity, the common goal is to drive the limiting ratio of input entropy divided by output entropy to 1, not merely \\(O(1)\\).
In this spirit, we consider how efficiently a sampler can achieve an expected entropy cost at most \\(H(\mathbf{p}_1)+\cdots+H(\mathbf{p}_n)+\varepsilon n + o(n)\\) for small \\(\varepsilon > 0\\), corresponding to an entropy ratio of \\(1 + O(\varepsilon)\\) if the target distributions have bounded entropy.

A common approach to improve entropy efficiency while retaining bounded space and efficient sampling is to batch samples together.
For example, we could run Knuth and Yao's optimal online algorithm for sampling from the first \\(\lceil 2/\varepsilon \rceil\\) distributions, then reset its internal state and repeat for the next \\(\lceil 2/\varepsilon \rceil\\) distributions, ad infinitum.
The expected entropy consumption of a single batch is bounded by \\(2\\) bits plus the entropy of the target distributions, and there are roughly \\(\varepsilon n / 2\\) batches.
Therefore, the entropy consumption of this batched method is bounded by \\(H(\mathbf{p}_1)+\cdots+H(\mathbf{p}_n)+\varepsilon n + o(n)\\), and the memory and sampling time are increased by a factor of \\(O(1/\varepsilon)\\) compared to the fully stateless approach.
This linear tradeoff between entropy efficiency and space/time complexity appears in several recent works, including [Lumbroso's Fast Dice Roller](https://doi.org/10.48550/arXiv.1304.1916) (section 3; only applicable to uniform sampling), [Kozen and Soloviev's restart protocols](https://doi.org/10.1016/j.jlamp.2021.100734), and [Shao and Wang's Michelangeroll](https://doi.org/10.48550/arXiv.2507.00915).
All of these methods intermittently reset the program state to the initial state \\(S_0\\) with zero information, which means that they have the same entropy loss bound of around \\(2\\) bits per batch.
Further, the memory required by these methods grows at least linearly in the batch size, hence the linear tradeoff.

## Problem statement {#problem-statement}

Our goal is to design a sampler with the optimal tradeoff between entropy efficiency and space complexity, as stated below.

> **Problem**:
> Design an online random sampling algorithm with expected entropy cost at most \\(H(\mathbf{p}_1)+\cdots+H(\mathbf{p}_n)+\varepsilon n + o(n)\\), with minimal expected space complexity as \\(\varepsilon \to 0\\).

<p></p>

# Our result {#our-result}

In this blog post, we solve the problem for the case of rational distributions with bounded denominators.

> **Theorem** (simplified):
> Let \\(\Delta_d\\) denote the set of rational distributions whose probabilities have common denominator at most \\(d\\).
> For any \\(\varepsilon > 0\\) and \\(d \geq 1\\), there exists an online random sampling algorithm such that, for every sequence \\(\mathbf{p}\_1, \mathbf{p}\_2, \ldots \in \Delta_d\\), the expected entropy cost of generating the first \\(n\\) outputs is at most \\(\sum_{i=1}^{n}H(\mathbf{p}\_i) + \varepsilon n + O(\log(d/\varepsilon))\\).
> The algorithm uses \\((2+o(1))\log(d/\varepsilon)\\) bits of persistent state and \\(O(\log(d/\varepsilon))\\) space during sampling.
> Any such algorithm requires at least \\(\Omega(\log(1/\varepsilon))\\) bits of persistent state, so our algorithm is optimal up to constant factors.

<p></p>

Our algorithms replace the previous linear dependence on \\(1/\varepsilon\\) with a logarithmic dependence.
Therefore, we achieve exponentially better space for the same entropy efficiency, or equivalently, exponentially better entropy efficiency for the same space, compared to all previous sampling methods for nonuniform discrete distributions.
For the special case of discrete uniform sampling (i.e., \\(\mathbf{p}\_0 = \cdots = \mathbf{p}\_{k-1} = 1/k\\)), a method with the same exponential tradeoff was first described in an [article by Jacques Willekens](https://web.archive.org/web/20200213145912/http://mathforum.org/library/drmath/view/65653.html), and subsequently rediscovered [several](https://doi.org/10.48550/arXiv.1012.4290) [times](https://doi.org/10.48550/arXiv.1412.7407).
This efficient uniform sampling algorithm maintains a state describing a discrete uniform random variable, which is propagated indefinitely across rounds, rather than periodically reset.
We show how discrete uniform state variables can also be used to recycle unused randomness from nonuniform samplers.

# Preliminaries: stateless sampling algorithms {#stateless-sampling-algorithms}

Our proposed online sampling algorithms build on classical algorithms for generating a single sample from a given distribution, which we now review.
Knuth and Yao's algorithm is based on DDG trees (discrete distribution generating trees), which represent sampling algorithms as binary trees, where at each internal node, the sampler flips a fair coin to decide which child node to visit next, and each leaf node corresponds to an outcome in the target distribution.
However, a general implementation of their method requires either exponential space to explicitly construct the DDG tree, or linear sampling runtime to implicitly traverse the tree.
Keith Schwarz wrote [a popular blog post](https://www.keithschwarz.com/darts-dice-coins/) investigating several sampling algorithms, but without regard to entropy efficiency, and under the assumption that exact operations on real numbers can be performed in constant time.
We have derived randomness recycling rules for many of these algorithms, but we will focus on the binary-search inversion method ("Roulette Wheel Selection" in Schwarz's blog post).

## Stateless nonuniform sampling {#stateless-nonuniform-sampling}

Say we want to generate a random number \\(X\\) with probabilities \\((0.2, 0.5, 0.3)\\) for outcomes \\((0, 1, 2)\\), respectively.
If we have access to a uniform random number over \\(10\\) outcomes, then we can map the first two outcomes to \\(0\\), the next five outcomes to \\(1\\), and the last three outcomes to \\(2\\), as illustrated in the following diagram.

![generating a nonuniform random number using the inversion method](standalone-nonuniform-example.png)

This approach generalizes to any discrete distribution with finite support and rational probabilities.
Assume that the target distribution is provided as a list of integer weights \\(a_0, a_1, \ldots, a_{k-1}\\), and the goal is to sample an index \\(i\\) with probability proportional to \\(a_i\\).
In particular, let \\(A_i = \sum_{j=0}^{i-1} a_j\\) denote the prefix sums; then the target probabilities are \\(p_i = a_i / A_{k}\\).
The inversion method samples a uniform random variable \\(U \sim \operatorname{Uniform}(\\{0,1,\ldots,A_{k}-1\\})\\) and returns the index \\(i\\) such that \\(A_{i} \leq U < A_{i+1}\\).

There are \\(a_i\\) possible values of \\(U\\) that yield outcome \\(i\\), so the probability of returning index \\(i\\) is exactly \\(a_i / A_{k}\\).
The following code implements inversion sampling, performing binary search (`bisect`) on the cumulative weights \\(\\{A_0, A_1, \ldots, A_k\\}\\), assuming access to a discrete uniform sampler `Uniform(m)` that generates a uniform random variable over the range \\(\\{0,1,\ldots,m-1\\}\\).

```python
def Inversion(A):
    U = Uniform(A[-1])
    X = bisect(A, U) - 1
    return X
```

## Stateless uniform sampling {#stateless-uniform-sampling}

Like `Inversion`, many general random sampling algorithms require a discrete uniform sampler as a subroutine.
Therefore, we now consider specialized algorithms for sampling from discrete uniform distributions.
Jérémie Lumbroso's [Fast Dice Roller](https://doi.org/10.48550/arXiv.1304.1916) generates a uniform over the \\(m\\) outcomes \\(\\{0,1,\ldots,m-1\\}\\) using \\(O(\log m)\\) space and \\(O(\log m)\\) expected time, while consuming fewer than \\(\log(m)+ 2\\) coin flips in expectation to produce a sample.
The idea is to maintain a pair of integers \\((Z,M)\\) satisfying \\(M > 0\\) and \\(Z \sim \operatorname{Uniform}(\\{0,1,\ldots,M-1\\})\\), i.e., a discrete uniform random state.
Here is a minor reformulation of the Fast Dice Roller, where `Flip()` is assumed to return a fair coin toss (0 or 1 with equal probability).

```python
def Uniform(m):
    Z = 0
    M = 1
    while True:
        while M < m:
            Z = 2 * Z + Flip()
            M = 2 * M
        if Z < m:
            return Z
        Z = Z - m
        M = M - m
```

Notice that the update `Z = 2 * Z + Flip()` and `M = 2 * M` maintains the invariant that \\(Z\\) is uniform over \\(\\{0,1,\ldots,M-1\\}\\), provided that `Flip()` returns a fair coin toss, independent of all previous coin flips.
Once \\(M \geq m\\), we can return a value \\(Z \sim \operatorname{Uniform}(\\{0,1,\ldots,m-1\\})\\) conditioned on \\(Z < m\\).
If instead \\(Z \geq m\\), we can rerun the algorithm with the updated state \\((Z-m, M-m)\\).

Although this `Uniform` algorithm is entropy optimal for a single sample (matching Knuth and Yao's entropy efficiency), it is far from optimal when called repeatedly in the online setting, because it does not maintain any random state between calls.
Because Knuth and Yao only guarantee a bound of \\(H(\mathbf{p})+2\\) coin flips for a single sample, `Uniform` wastes \\(\Theta(1)\\) coin flips per call.
In particular, after \\(n\\) calls to `Uniform` with parameters \\(m_1,\ldots,m_n\\), the expected number of coin flips used is bounded by \\(\sum_{i=1}^{n} \log(m_i) + 2n\\), significantly worse than the optimal bound of \\(\sum_{i=1}^{n} \log(m_i) + 2\\).

# Our approach: randomness recycling {#sampling-with-randomness-recycling}

In this section, we show how to modify `Uniform` to efficiently recycle randomness, and then generalize the recycling method to nonuniform sampling using the inversion method.

## Uniform sampling with randomness recycling {#uniform-sampling-with-randomness-recycling}

First, we need to understand where the entropy waste in `Uniform` comes from.
Lumbroso's analysis of `Uniform` shows that it is the comparison `if Z < m` that immediately causes a loss of up to one bit of entropy.
The uniform state over \\(M\\) outcomes is divided into two smaller states, over \\(m\\) or \\(M-m\\) outcomes, respectively.
This is equivalent to throwing away the information from a Bernoulli variable with parameter \\(m/M\\).
Further, each iteration of `while True` has a failure probability of \\(1-m/M\\), which can be up to \\(1/2\\), so the expected number of iterations is bounded by 2.
The information lost from the comparison `if Z < m` cannot be recovered, because the event \\(Z < m\\) has become correlated with the control flow of the program.
However, we can modify the algorithm to minimize the failure probability, by using a larger value of \\(M\\) before making a comparison.

To efficiently scale a discrete uniform over a large range \\(M\\) down to a smaller range \\(m\\), a standard technique is to use integer division.
The following diagram illustrates how to generate a uniform integer over \\(m = 10\\) outcomes given a uniform integer \\(Z\\) over \\(M = 32\\) outcomes, by writing \\(Z = 10 q_Z + r_Z\\), where \\(q_Z\\) is the quotient and \\(r_Z\\) is the remainder.
If \\(Z < 30\\), then \\(r_Z\\) is uniform as desired, and otherwise, we reject and continue the algorithm.

![example of generating a uniform integer using integer division](standalone-uniform-division-example.png)

It is important to note that the remainder \\(r_Z\\) is not uniformly distributed in general, which is why we need to reject when \\(q_Z = \lfloor M/m \rfloor\\), illustrated in the rightmost block of the diagram.
Further, conditioned on \\(q_Z < \lfloor M/m \rfloor\\), the quotient \\(q_Z\\) is uniform over \\(\lfloor M/m \rfloor\\) outcomes and independent of the return value \\(r_Z\\), so this discrete uniform variable can be stored and used to improve the entropy efficiency of future calls to the sampling algorithm.
Here is pseudocode for our full algorithm for online uniform sampling.

```python
Z = 0
M = 1
M_target = 9223372036854775808
def Uniform_Recycling(m):
    global Z, M, M_target
    while True:
        while M < M_target:
            Z = 2 * Z + Flip()
            M = 2 * M
        qM, rM = divmod(M, m)
        qZ, rZ = divmod(Z, m)
        if qZ < qM:
            Z = qZ
            M = qM
            return rZ
        Z = rZ
        M = rM
```

The state variables `Z, M` represent a discrete uniform random variable, containing recycled randomness, independent of the previous outputs from the algorithm.
We use the term "randomness recycling" to describe how random information (obtained through `Flip()`) is stored for use when generating future samples.
The parameter `M_target` should be much larger than any `m` that will be sampled, to ensure that the rejection probability is small.
For example, if `m` is always a 32-bit integer, then `M_target = 9223372036854775808` (which is \\(2^{63}\\)) ensures that the rejection probability is less than \\(2^{-31}\\), while also ensuring that all program variables fit in 64-bit integers.

Although the division operation in `Uniform_Recycling` is more expensive than the simple arithmetic operations in `Uniform`, the increased entropy efficiency in `Uniform_Recycling` more than makes up the difference when randomness is expensive.
As a typical example where randomness is treated as a scarce resource, the website [RANDOM.ORG](https://www.random.org) uses an algorithm similar to `Uniform_Recycling` for precisely this reason.
This `Uniform_Recycling` is essentially identical to [the algorithm proposed by Jacques Willekens](https://web.archive.org/web/20200213145912/http://mathforum.org/library/drmath/view/65653.html).
Next, we will generalize the randomness recycling technique to nonuniform sampling.

## Nonuniform sampling with randomness recycling {#nonuniform-sampling-with-randomness-recycling}

Recall the `Inversion` method [discussed earlier](#stateless-nonuniform-sampling), which samples from a nonuniform distribution by first sampling a uniform random variable and then performing a binary search on the cumulative weights.
We can improve the entropy efficiency by simply replacing the call to `Uniform` with `Uniform_Recycling`, but this alone does not bring us close to the optimal entropy efficiency, because the uniform variable contains \\(\log(A_k)\\) bits of entropy, whereas the output entropy is only \\(H(\mathbf{p}) \leq \log(k)\\).
Therefore, we need to also recycle the leftover information from the original uniform variable which was not needed to determine the output \\(X \sim \mathbf{p}\\).
Recall the image of how the inversion method splits up the uniform variable values into segments.

![generating a nonuniform random number using the inversion method](standalone-nonuniform.png)

Conditioning on the event that \\(U\\) falls in the range \\(\\{A_i, \ldots, A_{i+1}-1\\}\\), we obtain a new uniform random state given by \\(Z^\prime = U - A_i\\) and \\(M^\prime = a_i\\), satisfying \\(Z^\prime \sim \operatorname{Uniform}(\\{0,1,\ldots,M^\prime-1\\})\\).
We can recycle \\((Z^\prime,M^\prime)\\) back into the global state variables \\((Z,M)\\) using a standard trick for merging two independent uniform random states, namely, setting \\(Z \leftarrow Z + Z^\prime \cdot M\\) and \\(M \leftarrow M \cdot M^\prime\\).
The full pseudocode for the inversion method with randomness recycling is as follows.

```python
def Inversion_Recycling(A):
    U = Uniform_Recycling(A[-1])
    X = bisect(A, U) - 1
    Z1 = U - A[X]
    M1 = A[X+1] - A[X]
    global Z, M
    Z = Z + Z1 * M
    M = M * M1
    return X
```

The conversion from `U` to `X, Z1, M1` is reversible, and in particular it does not lose any entropy.
Therefore, the only entropy loss in `Inversion_Recycling` comes from the call to `Uniform_Recycling`, and `Inversion_Recycling` inherits the same entropy efficiency as `Uniform_Recycling`.

## Information flow {#information-flow}

Entropy efficiency can be understood as the amount of source information (randomness from the input coin `Flip()`) that ends up in the output samples.
Information flow diagrams help us analyze entropy efficiency by illustrating how the random information flows through the program.
At a high level, the classical inversion method for nonuniform sampling first converts coin flips to a discrete uniform random variable over a certain range, and then transforms the uniform into a sample from the target distribution, as shown in the following diagram.

![stateless inversion diagram](standalone-diagram.png)

Our proposed algorithms build on this same underlying structure, using deterministic transformations of uniform random variables, but we add randomness recycling rules to carry over unused randomness from round to round.
Our recycled random states are all discrete uniform random variables, represented as pairs of integers \\(Z,M\\) such that \\(Z \sim \operatorname{Uniform}(\\{0,1,\ldots,M-1\\})\\).
These discrete uniform states are convenient to work with, because merging and splitting operations are as simple as integer multiplication and division.
The following diagram illustrates the information flow in one round of our online sampling algorithm, where we have essentially added a recycling loop to the classical inversion method.

![randomness recycling inversion diagram](standalone-diagram-rr.png)

# Entropy and space analysis {#analysis}

We now analyze our algorithms to prove the claimed bounds.
We first analyze the entropy cost of `Uniform_Recycling`.
Let \\(m_{\max}\\) denote the largest value of \\(m\\) passed to `Uniform_Recycling` over the entire execution, and let \\(M_{\min}\\) denote the smallest possible value of \\(M\\) before division (written as `M_target` in the pseudocode).
Then the rejection probability in `Uniform_Recycling` is less than \\(m_{\max}/M_{\min}\\), so the expected number of iterations of the outer `while True` loop is less than \\(1/(1 - m_{\max}/M_{\min})\\).
Further, the entropy lost per iteration is given by the entropy of the accept-reject decision, which is bounded by the binary entropy function \\(H_{\rm b}(m_{\max}/M_{\min})\\).
Multiplying the bounds on the expected number of iterations and the entropy lost per iteration, the overall entropy loss per call to `Uniform_Recycling` is bounded by
\\[
\frac{H_{\rm b}(m_{\max}/M_{\min})}{1 - m_{\max}/M_{\min}}
= \frac{m_{\max}}{M_{\min}-m_{\max}} \log(M_{\min}/m_{\max}) - \log(1 - m_{\max}/M_{\min}).
\\]
Given a bound on the size of the input integers \\(m_{\max}\\), to find a value of \\(M_{\min}\\) that achieves a desired entropy loss \\(\varepsilon > 0\\), it suffices to solve the transcendental equation
\\[
\varepsilon = \frac{m_{\max}}{M_{\min}-m_{\max}} \log(M_{\min}/m_{\max}) - \log(1 - m_{\max}/M_{\min})
\\]
for \\(M_{\min}\\).
The solution grows as \\(M_{\min} = m_{\max} \cdot \tilde{O}(1 / \varepsilon)\\) as \\(\varepsilon \to 0\\), which means that the required integer size \\(1+\lceil\log M_{\min}\rceil\\) grows as \\(O(\log(m_{\max}/\varepsilon))\\).

For nonuniform sampling, `Inversion_Recycling` has the same entropy loss as `Uniform_Recycling`.
The following table compares the entropy/space efficiency of our method with the Knuth and Yao method, either statelessly (using a fresh start for each new sample), fully online, or batched (online, but resetting the state every \\(\lceil 2/\varepsilon \rceil\\) iterations) as described in the [online random sampling](#online-random-sampling) section.

| Method                    | Amortized Entropy Loss Bound | Persistent Space             |
|:------------------------- | ---------------------------- | ---------------------------- |
| Knuth and Yao (Stateless) | 2                            | 0                            |
| Knuth and Yao (Online)    | 0                            | unbounded                    |
| Knuth and Yao (Batched)   | \\( \varepsilon \\)          | \\(O(1/\varepsilon)\\)       |
| `Inversion_Recycling`     | \\( \varepsilon \\)          | \\(O(\log(1/\varepsilon))\\) |

In [more recent work](https://doi.org/10.48550/arXiv.2607.14503), we have proven that our space complexity is optimal up to constant factors.
Namely, any online sampling algorithm achieving an amortized entropy loss bound of \\(\varepsilon\\) requires \\(\Omega(\log(1/\varepsilon))\\) bits of persistent state.

# Evaluation {#evaluation}

We implemented the `Inversion_Recycling` algorithm in C and compared its performance to the standard inversion method, which does not recycle randomness using a random state such as \\((Z,M)\\).
We generated several distributions with varying numbers of outcomes, and for each distribution, we preprocessed the prefix sums and sampled 1 million times from the distribution using each algorithm.
The following figure shows the performance improvement from randomness recycling, in terms of both entropy consumption and runtime, using `/dev/random` as the source of randomness.
The blue points represent the original method, and the orange points represent our method with randomness recycling.

![performance improvement from randomness recycling](standalone-performance.png)

We also applied the same randomness recycling technique to accelerate the following algorithms:

- [Lemire's uniform sampler](https://doi.org/10.1145/3230636),
- [Brackett-Rozinsky and Lemire's batched uniform sampler](https://doi.org/10.1002/spe.3369),
- [Walker's alias method with Vose's modification](https://doi.org/10.1109/32.92917),
- [the Fast Loaded Dice Roller](https://doi.org/10.48550/arXiv.2003.03830), and
- [the Amplified Loaded Dice Roller](https://doi.org/10.48550/arXiv.2504.04267).

Different algorithms have different tradeoffs between space and runtime, but of particular note is the alias method, described in detail in [Schwarz's blog post](https://www.keithschwarz.com/darts-dice-coins/), which requires linear space and a constant number of operations per sample.
By applying randomness recycling to the alias method, we can achieve the same linear space complexity and constant number of sampling operations; the tradeoff is that the integers used while sampling require an additional \\(O(\log(1/\varepsilon))\\) bits of precision to achieve an amortized entropy loss of \\(\varepsilon\\), and we need to propagate the state of size \\(O(\log(1/\varepsilon))\\) between rounds.

# Applications {#applications}

Our entropy-efficient exact online sampling algorithms are useful in any application requiring high-quality randomness.
Random number service providers must provide true random numbers to many users, where each user receives numbers independent of the others.
Hence, it would be easy to exhaust a true random source using inefficient sampling algorithms.
Using our generalized randomness recycling methods, it is now possible for random number service providers or library developers to achieve optimal entropy efficiency and space complexity for sampling nonuniform distributions.

# Conclusion {#conclusion}

We have demonstrated how randomness recycling enables entropy-efficient online random sampling with asymptotically optimal space complexity.
For further details, please see the [full paper](https://doi.org/10.48550/arXiv.2505.18879).
This article is based on joint work with [Feras Saad](https://www.cs.cmu.edu/~fsaad/), presented at the [2026 Symposium on Discrete Algorithms](https://doi.org/10.1137/1.9781611978971.89).
Our more recent work [proves the optimality](https://doi.org/10.48550/arXiv.2607.14503) of our space complexity.
In collaboration with [David G. Harris](https://sites.google.com/site/davidgharriswebsite/home), we have also [extended our method](https://doi.org/10.48550/arXiv.2607.13828) to optimally sample from distributions with arbitrary real probabilities.

[^log]: We use \\(\log\\) to denote the logarithm using base 2, so that the entropy is measured in bits.

[^index]: In contrast to the probability weights, the indices on the sequence of distributions are not represented in the computer, only implicitly used for the mathematical analysis, hence the one-based indexing.
