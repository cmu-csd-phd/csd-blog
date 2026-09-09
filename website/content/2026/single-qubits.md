+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "Quantum Hypothesis Testing with Simple Measurements"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2026-02-24

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Theory"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
# Consider these similar to keywords specified for a research paper.
tags = ["quantum", "hypothesis testing"]

[extra]
author = {name = "William He", url = "https://wrhe.github.io./" }
# The committee specification is  a list of objects similar to the author.
committee = [
    {name = "William Kuszmaul", url = "https://sites.google.com/site/williamkuszmaul"},
    {name = "Yang Liu", url = "https://yangpliu.github.io/"},
    {name = "Noah Singer", url = "https://noahsinger.org/"}
]
+++

# Certifying a Point Mass?
This blog post is about hypothesis testing. In the classical world, this task is often modeled in the following way: we, as scientists, have formed the belief that some (random) system follows a _hypothesis distribution_ \\( \mu\\). For example, we may believe that some many-sided die is fair, or we may believe that some ensemble of magnetized particles follows a certain statistical physics model. Then, we are given observations from the system: rolls of the die or observations of the magnetization of particles, and we must decide whether to reject the hypothesis or not. 

More formally, if we are given samples from some unknown distribution \\(\pi\\), we would like to:

1. Reject \\(\pi\\) if \\(d(\pi,\mu)\\) is large, where \\(d\\) is some measure of distance between distributions.

2. Accept if \\(\pi=\mu\\).

Today we are going to be studying a trivial version of this problem: the case where the hypothesis distribution \\(\mu\\) is a point mass on a certain outcome \\(x\\). The best thing one can do then is to reject if and only if some outcome drawn from \\(\pi\\) is not \\(x\\).

The twist is that we are going to study the quantum version of this problem, which contains a richer mathematical theory. In short, when a system is quantum mechanical, the tester can choose how the "observations" are made, and with the full power of quantum computers, we could implement the above algorithm for certifying a point mass. But when we restrict ourselves to making more realistic measurements (limited by our quantum-computational capabilities), it is not so clear what to do. So let me tell you what I mean by this.

# Quantum Many-Body Systems and Measurements

The most simple quantum system is a _qubit_. A qubit models a system (maybe think of this as a single particle) with two states, which we will denote \\(\ket{0}\\) and \\(\ket{1}\\). An interesting aspect of quantum mechanics is that this single particle need not exist exclusively as exactly \\(\ket{0}\\) or exactly \\(\ket{1}\\): a general description of a qubit's state is that of _superpositions_ of \\(\ket{0}\\) and \\(\ket{1}\\). That is, \\(\ket{0}\\) and \\(\ket{1}\\) are thought of as the standard orthonormal basis for \\(\mathbb{C}^2\\), and a general quantum qubit state is a unit vector in this space. We also call \\(\lbrace \ket0, \ket1\rbrace\\) the _computational basis_ for \\(\mathbb{C}^2\\).

Given a qubit that is currently in the state \\(\ket{\psi}=\alpha_0 \ket{0}+\alpha_1\ket{1}\\), we can perform _measurements_ on the state. Measurements are made by specifying some orthonormal basis \\(\lbrace \ket{a},\ket{b}\rbrace\\) of \\(\mathbb{C}^2\\). Measuring in this particular basis will yield the outcome "\\(\ket{a}\\)" with probability \\(|\braket{\psi|a}|^2\\) and outcome "\\(\ket{b}\\)" with probability \\(|\braket{\psi|b}|^2\\). After the measurement, the state will _collapse_ into the state that was observed. Note that these probabilities sum to 1 because \\(\ket{\psi}\\) is a unit vector.

This is how you describe single-qubit states. But we are interested in quantum systems that contain many particles! How are these described? If you have \\(n\\) particles, each modeling a qubit, then the joint state of these particles is described by an _arbitrary_ unit vector in \\(\mathbb{C}^{2^n}\\), with \\(\lbrace \ket{x} : x \in \lbrace 0,1\rbrace^n \rbrace\\) forming an orthonormal basis for this space, also called the computational basis. This is much like in classical probability theory, where a general _distribution_ describing an \\(n\\)-coin system is an arbitrary convex combination of point masses of outcomes \\(x \in \lbrace 0,1\rbrace^n\\).

<div style="border:1px solid #4a90e2; padding:1em; border-radius:6px; background:#f7fbff">
<strong>Remark on Notation.</strong>
<p>
We will denote quantum states (normalized vectors in \(\mathbb{C}^{2^n}\)) by "kets" like \(\ket{\psi}\). We will write inner products between two kets \(\ket{\psi_1}\) and \(\ket{\psi_2}\) in the following way: \(\braket{\psi_1|\psi_2}\). The "bra" part \(\bra{\psi_1}\) should be regarded as a row vector that is the conjugate transpose of \(\ket{\psi_1}\). As in: \(\bra{\psi_1}=\ket{\psi_1}^\dagger\)
</p>
</div>

Moreover, we measure distance between quantum states using _fidelity_:

<div style="border:1px solid #4a90e2; padding:1em; border-radius:6px; background:#f7fbff">

<strong>Definition of Fidelity.</strong>
<p>
The fidelity between two quantum states \(\ket{\mu}\) and \(\ket{\pi}\) is equal to the squared inner product between the two vectors: \(|\braket{\mu|\pi}|^2\). The infidelity is equal to 1 minus the fidelity, and this is the measure of distance between quantum states we consider in this blog post.
</p>

</div>
Note that we regard states that are the same up to a global scalar as the same state, since they are not distinguishable under any measurements.

One can simulate a classical probability distribution described by probabilities \\(p_x\\) on \\(\lbrace 0,1\rbrace^n\\) using an \\(n\\)-qubit quantum state \\(\sum_x \sqrt{p_x} \ket{x}\\), measured in the computational basis \\(\lbrace \ket{x}:x\in\lbrace 0,1\rbrace^n\rbrace\\). 

But quantum mechanics gives us more power than just measuring in this standard basis. Just as we could measure a single qubit in any orthonormal basis for \\(\mathbb{C}^2\\), we can measure an \\(n\\)-qubit system in an arbitrary orthonormal basis for \\(\mathbb{C}^{2^n}\\)! This is what makes certifying quantum states tantamount to certifying classical point masses: in order to test if a system is in the hypothesis state \\(\ket{\mu}\\), one need only measure the unknown state \\(\ket{\pi}\\) in an orthonormal basis for \\(\mathbb{C}^{2^n}\\) in which \\(\ket{\mu}\\) is a basis vector. This is the optimal certification algorithm!

## The Trouble with the Point-Mass Testing Algorithm

The problem with this optimal certification algorithm is that performing the measurement in the basis containing \\(\ket{\mu}\\) is _as hard as preparing \\(\ket{\mu}\\)_ using a quantum computer. We do not have very good quantum computers and are currently incapable of preparing many of the states we would like to prepare. Thus, a natural question is whether one can design certification algorithms not making such complicated measurements. The problem with the optimal measurement algorithm is that it requires us to essentially view the entire \\(n\\)-qubit system using a single observation, in a very global manner. We are interested in designing certification algorithms that observe the single particles one at a time. Before explaining how to formalize these _partial measurements_, let me first say what we do.

## Previous Work and Our Results

The task of quantum state certification has received much attention in the literature. Studying algorithms using single-qubit measurements is also common. Previous algorithms required either i) exponentially many copies of the unknown state \\(\ket{\pi}\\) or ii) a restriction on the type of hypothesis state \\(\ket{\mu}\\) that could be certified. See, for example, works of ([Flammia-Liu](https://arxiv.org/abs/1104.4695)), ([Huang-Preskill-Soleimanifar](https://arxiv.org/abs/2404.07281)). Huang et al. even asked for constructions of states \\(\ket{\mu}\\) with no efficient certification algorithms using single-qubit measurements.

In a recent [paper](https://arxiv.org/abs/2506.11355), Meghal Gupta, Ryan O'Donnell, and I showed that there _does not exist_ such a state. We give an efficient algorithm for certifying any quantum state using just single-qubit measurements:

<div style="border:1px solid #4a90e2; padding:1em; border-radius:6px; background:#f7fbff">

<strong>Theorem 1.</strong>
<p>
There exists an algorithm that given a description of any \(n\)-qubit hypothesis state \(\ket{\mu}\) and \(O(n/\epsilon)\) copies of an unknown state \(\ket{\pi}\), makes single-qubit measurements to the copies of \(\ket{\pi}\) and satisfies the following:

1. If \\(|\langle \pi \mid \mu \rangle|^2 = 1\\), then the algorithm always accepts.
2. If \\(|\langle \pi \mid \mu \rangle|^2 \le 1 - \epsilon\\), then the algorithm rejects with probability at least 0.99.

</p>

</div>

In the rest of this blog post, I will tell you about the design of this algorithm.


# Proof of Theorem 1

## Partial Measurements
First I should to tell you about how one formalizes partial measurements to a quantum system. What happens when you have an \\(n\\)-qubit system and you measure the first qubit? To answer this, write 

$$\ket{\pi} = \sum_{x:x_1=0}\alpha_x \ket{x}+ \sum_{x:x_1=1}\alpha_x \ket{x}=\sum_{x\in\lbrace 0,1\rbrace^{n-1}}\alpha_{0x} \ket{0x}+ \sum_{x\in\lbrace 0,1\rbrace^{n-1}}\alpha_{1x} \ket{1x}$$

A helpful way to rewrite this will be to "factor out" the first qubit in each basis vector 

$$\ket{\pi} = \ket{0}\otimes \sum_{x\in\lbrace 0,1\rbrace^{n-1}}\alpha_{0x} \ket{x}+\ket{1}\otimes \sum_{x\in\lbrace 0,1\rbrace^{n-1}}\alpha_{1x} \ket{x} = \ket{0}\otimes u_0 + \ket{1}\otimes u_1$$

Then, measuring the first qubit in the computational basis will yield the outcome "\\(\ket{0}\\)" with probability \\(\||u_0\||^2\\); this will collapse the state into 
$$\frac{ \ket{0}\otimes u_0}{\||u_0\||^2} \eqqcolon \ket{0}\otimes \ket{\pi_0}.$$
The outcome "\\(\ket{1}\\)" occurs with probability \\(\||u_1\||^2\\), and this collapses the state into
$$\frac{ \ket{1}\otimes u_1}{\||u_1\||^2} \eqqcolon \ket{1}\otimes \ket{\pi_1}.$$

We have essentially recovered the ideas of conditional probability. This tells the story for computational basis measurements, but there is actually nothing special about the computational basis. The beauty of quantum mechanics is that we can measure in bases besides the computational basis. 

If \\(\lbrace \ket{a},\ket{b}\rbrace \\) is an orthonormal basis for \\(\mathbb{C}^{2}\\) then we can always write
$$\ket{\pi} = \ket{a}\otimes u_a + \ket{b}\otimes u_b$$
Measuring the first qubit in the \\(\lbrace \ket{a},\ket{b}\rbrace\\) basis yields the outcome "\\(\ket{a}\\)" with probability \\(\||u_a\||^2\\); this will collapse the state into \\(\frac{ \ket{a}\otimes u_a}{\||u_a\||^2}\\). The outcome "\\(\ket{b}\\)" occurs with probability \\(\||u_b\||^2\\); this will collapse the state into \\(\frac{ \ket{b}\otimes u_b}{\||u_b\||^2}\\).

This generalizes to measuring many qubits as follows. Suppose \\(S\subseteq [n]\\) is a set of qubits, and let \\(\lbrace\ket{a_x}\rbrace_{x\in \lbrace 0,1\rbrace^{S}}\\) form an orthonormal basis for \\(\mathbb{C}^{2^{|S|}}\\). We can write

$$\ket{\pi}=\sum_{i=1}^{2^{|S|}} \ket{a_i} \otimes u_i.$$

Then the outcome \\(i\\) occurs with probability equal to \\(\||u_i\||^2\\) and collapses the state to \\(\ket{a_i}\otimes \ket{\pi_u}\\). 



## The Algorithm

Now let me tell you the general framework the algorithm follows. Given a single copy of the unknown state \\(\ket{\pi}\\), it does the following:

1. Choose \\(k=1,\dots,n\\) uniformly at random, and measure the first \\(k-1\\) qubits of \\(\ket{\pi}\\) in the \\(\ket{0},\ket{1}\\) basis. 
2. This yields some outcome \\(x\in \lbrace 0,1\rbrace^{k-1}\\) and a reduced state \\(\ket{\pi_x}\\) on the remaining qubits.
3. Check whether \\(\ket{\pi_x}\\) satisfies some property that \\(\ket{\mu_x}\\) satisfies. 

This property to which I am referring in this last point is going to be something about the relationship between the further-conditioned states. We are going to check whether something like the following analogy holds: \\(\ket{\mu_{x0}}\\) is to \\(\ket{\mu_{x1}}\\) as \\(\ket{\pi_{x0}}\\) is to \\(\ket{\pi_{x1}}\\).

Intuitively, we can think of an \\(n\\)-qubit quantum state \\(\ket{\pi}=\sum_x \alpha_x \ket{x}\\) as corresponding to a complete binary tree of depth \\(n\\), where the leaf nodes correspond to length-\\(n\\) strings and are labeled by the amplitudes \\(\alpha_x\\). What is going on here is that we are selecting a random internal node in this tree, and checking that the conditional states on the left and right subtrees out of this internal node satisfy some kind of relationship.

We want to design some subtest that works with \\(\ket{\pi_x}\\), and rejects this state if this analogy does not hold, while always accepting if it does hold. Mathematically, we can write

$$\ket{\mu_x} = \ket{0}\otimes u_{x0} + \ket{1}\otimes u_{x1} \text{ and }\ket{\pi_x}=\ket{0}\otimes v_{x0}+\ket{1}\otimes v_{x1}.$$

Note here that the \\(u\\)s and \\(v\\)s are not necessarily quantum states because they are not necessarily normalized. To emphasize this we have dropped the ket notation.

Then the degree to which the analogy holds is quantified using the following quantity:

$$
\mathrm{err}_x :=
\left|
  \frac{\left\|{u_x}_1\right\|^2}{\left\|{u_x}_0\right\|^2}\, {u_x}_0^\dagger {v_x}_0
  +
  \frac{\left\|{u_x}_0\right\|^2}{\left\|{u_x}_1\right\|^2}\, {u_x}_1^\dagger {v_x}_1
\right|^2
$$



This is a scary-looking quantity, but we can build intuition using an example. 

Let \\(\ket{\mu}=\frac1{\sqrt2}\ket{00}+\frac1{\sqrt2}\ket{11}\\), also known as the Bell pair.

Let \\(\ket{\pi} =\frac1{\sqrt2}\ket{00} - \frac1{\sqrt2}\ket{11}\\), so that \\(\ket{\mu}\perp \ket{\pi}\\). We can compute that \\(\mathrm{err}_x = 1\\) if \\(x\\) is the empty string, and for all other \\(x\\), \\(\mathrm{err}_x = 0\\). That is, 

$$\mathrm{err}_{\emptyset} = \| u_0^\dagger v_0 + u_1^\dag v_1 \|^2 =  \| \frac12 \braket{0|0} - (-\frac12\braket{1|1}) \|^2=1$$

On the other hand, for \\(x\in \lbrace 0,1\rbrace\\), we have no error because for such \\(x\\), we have \\(\ket{\pi_x}=\ket{\mu_x}=\ket{x}\\). 

What this is saying is that all of the distance between \\(\ket{\mu}\\) and \\(\ket{\pi}\\) can be attributed to this sign difference between the left and right subtrees at the root of the binary tree that describes the states.

In general, \\(\mathrm{err}_x\\) captures how much of the distance between \\(\ket{\mu}\\) and \\(\ket{\pi}\\) can be assigned to each internal node in the tree. The mathematical fact that formalizes this is:


<div style="border:1px solid #4a90e2; padding:1em; border-radius:6px; background:#f7fbff">

<strong>Lemma 1.</strong>
<p>
\(\mathbb{E}_x[\mathrm{err}_x] = \frac{1 - |\braket{\mu|\pi}|^2}{n}\), where the expectation is over drawing \(x\) by sampling \(k=1,\dots,n\) uniformly at random and measuring the first \(k-1\) qubits of the state \(\ket{\pi}\) in the computational basis.
</p>

</div>


This lemma can be proved by induction on \\(n\\), but we omit the proof here.


Thus, if we can design a subtest that given \\(\ket{\pi_x}\\), can make single-qubit measurements to \\(\ket{\pi_x}\\) and reject with probability at least \\(\mathrm{err}_x\\), all while accepting when \\(\ket{\pi}=\ket{\mu}\\), then our single-copy tester will have the following guarantees:

1. If \\(\ket{\mu}=\ket{\pi}\\), then the algorithm always accepts.
2. If \\(1-|\braket{\mu|\pi}|^2 \geq \epsilon\\) then the algorithm rejects with probability at least \\(\epsilon/n\\), since
$$\mathbf{Pr}[\text{reject}]= \mathbb{E}_x[\mathbf{Pr}[\text{reject}|x]] \geq \mathbb{E}_x[\mathrm{err}_x] \geq \epsilon/n.$$

Repeating this test on \\(O(n/\epsilon)\\) copies and accepting if and only if all testers accept would then complete the proof of Theorem 1. So let's get to designing the subtest.


## The Subtest

Recall that we want to give a subtest that does the following, given a description of an \\(n-k+1\\)-qubit state
$$\ket{\mu_x}=\ket{0}\otimes u_{x0} + \ket{1}\otimes u_{x1}$$
and a single copy of another state 
$$\ket{\pi_x}=\ket{0}\otimes v_{x0} + \ket{1}\otimes v_{x1},$$
makes single-qubit measurements to the copy of \\(\ket{\pi_x}\\) and:
1. If \\(|\braket{\mu_x|\pi_x}|^2=1\\) then the subtest should always accept.
2. The subtest should reject with probability at least \\(\mathrm{err}_{x} = \| \frac{\||{u_x}_1\||^2}{\||{u_x}_0\||^2} {u_x}_0^\dag{v_x}_0 + \frac{\||{u_x}_0\||^2}{\||{u_x}_1\||^2}{u_x}_1^\dag {v_x}_1 \|^2\\).

Since we are only allowed single-qubit measurements, a natural plan is:
1. Make measurements in some basis to the last \\(n-k\\) qubits of \\(\ket{\pi_x}\\).
2. If \\(\ket{\pi}\\) were equal to \\(\ket{\mu}\\) then the remaining qubit (qubit \\(k\\)) would be in some state \\(\ket{\mu'}\\), so measure the last qubit in a basis \\(\{\ket{\mu'},\ket{\mu'}^\perp\}\\), accepting if and only if we see the outcome \\(\ket{\mu'}\\). 

Intuitively, we want that any discrepancy between \\(\ket{\pi_x}\\) and \\(\ket{\mu_x}\\) be "pushed up" to the \\(k\\)th qubit after the measurement. So what kind of measurements to the last \\(n-k\\) qubits of \\(\ket{\pi_x}\\) will be good for pushing up this discrepancy? Let's revisit our previous example of the Bell pair.

Recall that we set \\(x=\emptyset\\) so that \\(\ket{\mu_x}=\ket{\mu}=\frac1{\sqrt2}\ket{00}+\frac1{\sqrt2}\ket{11}\\) and \\(\ket{\pi_x}=\ket{\pi}=\frac1{\sqrt2}\ket{00}-\frac1{\sqrt2}\ket{11}\\). If we are to follow the plan above, we need to make a measurement of the second qubit in a way so that the difference between the "+" and "-" appears in the conditioned state on the first qubit. If we measure the second qubit of \\(\ket{\pi}\\) in the computational basis, then you can check that if you get outcome "\\(\ket{x}\\)" then the first qubit will also be in the state "\\(\ket{x}\\)", up to the undetectable global phase. But the same thing happens when you measure \\(\ket{\mu}\\), so this test cannot detect this sign difference.

The reason for this is because measuring the second qubit in the computational basis destroys one of the branches of the tree. If you get the outcome "\\(\ket{0}\\)" then the branch corresponding to "\\(\ket{1}\\)" vanishes from the resulting conditional state. What we need is a measurement of the second qubit that always keeps the two branches alive to an equal extent.

It turns out that in this particular case, it is a good idea to measure the second qubit in the following basis:
$$\ket{+} = \frac1{\sqrt2}\ket{0}+\frac1{\sqrt2}\ket{1} , \qquad \ket{-}=\frac1{\sqrt2}\ket{0}-\frac1{\sqrt2}\ket{1} .$$
If you measure the second qubit of \\(\ket{\pi}\\) in this basis, then getting an outcome of "\\(\ket{+}\\)" yields a first qubit in state \\(\ket{-}\\), and if you get "\\(\ket{-}\\)" then the first qubit collapses to state \\(\ket{+}\\). This is the exact opposite of what happens if you had done the same with \\(\ket{\mu}\\), where an outcome of "\\(\ket{+}\\)" collapses the first qubit to \\(\ket{+}\\) and an outcome of "\\(\ket{-}\\)" collapses the first qubit to \\(\ket{-}\\).

The reason this test works so well is because both branches of the tree out of the root node were treated fairly under this measurement. It turns out that to generalize this intuition, one simply needs to measure the last \\(n-k\\) qubits of \\(\ket{\pi}\\) in a basis in which \\(\ket{\mu_{x0}}\\) and \\(\ket{\mu_{x1}}\\) yield equally likely outcomes. Constructing such a measurement protocol can be done inductively, going one qubit at a time, but that is slightly beyond the scope of this blog post. 

## Final Algorithm
To summarize, the final algorithm proceeds as follows:
1. Choose \\(k=1,\dots,n\\) uniformly at random, and measure the first \\(k-1\\) qubits of \\(\ket{\pi}\\) in the \\(\ket{0},\ket{1}\\) basis. 
2. This yields some outcome \\(x\in  \lbrace 0,1 \rbrace^{k-1}\\) and a reduced state \\(\ket{\pi_x}\\) on the remaining qubits.
3. Measure the last \\(n-k\\) qubits of \\(\ket{\pi_x}\\) in a basis that yields equally likely outcomes for both \\(\ket{\mu_{x0}}\\) and \\(\ket{\mu_{x1}}\\). This gives outcome \\(\ell\\).
4. Let \\(\ket{\mu'}\\) be the reduced state on the \\(k\\)th qubit, had \\(\ket{\mu}\\) been measured to yield outcomes \\(x\\) and \\(\ell\\). 
5. Measure in the basis \\(\{\ket{\mu'},\ket{\mu'}^\perp\}\\), accepting if and only if we see the outcome \\(\ket{\mu'}\\). 


## Conclusion and Perspective
I feel there are a few takeaways from our work. The first one is simply that even the most basic questions in classical learning theory can be surprisingly mathematically rich in the quantum setting. In some sense, quantum learning is inherently active learning, due to the choice of measurements one can make.

A slightly more technical and personal perspective is that our test is an illustration of some kind of local-to-global phenomenon. By measuring local subsystems, one can obtain information about more global structure. If you are familiar with the notion of spectral gaps and Markov chain mixing, you may see resemblances between our breakdown of the infidelity into contributions from internal nodes in a tree and proofs of spectral gaps via inductive/localization-based arguments. Our analysis can be likened to the proof that the standard random walk on the hypercube has a spectral gap that is \\(\Omega(1/n)\\). I feel this perspective may be useful when further studying quantum statistical algorithms with restricted local measurements.

