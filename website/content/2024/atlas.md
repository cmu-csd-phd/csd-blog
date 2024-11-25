+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "Atlas: Hierarchical Partitioning for Quantum Circuit Simulation on GPUs"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2024-11-24

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Systems"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
# Consider these similar to keywords specified for a research paper.
tags = ["parallel programming", "quantum computing", "quantum simulation"]

[extra]
author = {name = "Mingkuan Xu", url = "https://mingkuan.taichi.graphics" }
# The committee specification is  a list of objects similar to the author.
committee = [
    {name = "Elaine Shi", url = "http://elaineshi.com"},
    {name = "Tianqi Chen", url = "https://tqchen.com/"},
    {name = "Mingxun Zhou", url = "https://wuwuz.github.io/"}
]
+++

# Background: Quantum Circuit Simulation

## Introduction
In the current Noisy Intermediate-Scale Quantum (NISQ) era, quantum computers are a scarce resource, and they suffer from decoherence and lack of error correction. Therefore, there is significant interest in quantum circuit simulation which enables performing robust quantum computation on classical parallel machine, and helps develop and debug quantum algorithms.

There are many methods to simulate quantum circuits. This blog post focuses on the *state-vector* (Schrödinger style) simulation, the most general, straightforward, and well-studied method. Some other techniques for noise-free accurate quantum circuit simulation include:

- Feynman-path simulation, which is good for sparse circuits;
- Tensor network simulation, which is good for circuits with low entanglement;
- Stabilizer simulation, which is good for Clifford circuits.

These methods are usually used for circuits with certain structures, or circuits with too many qubits (> 40) that are beyond the capability of state-vector simulation. For general circuits with good "quantumness" (hard to simulate using a classical computer), state-vector simulation is usually the most efficient approach. Our work aims to make it even more efficient.

## Quantum State and State Vector
State-vector simulation features a direct representation of the quantum state. The state \\(\ket{\psi}\\) of an \\(n\\)-qubit quantum circuit can be represented by a superposition of its *basis states* denoted \\(\ket{0\dots 00}\\), \\(\ket{0\dots 01}\\), ..., \\(\ket{1\dots 11}\\), written as
$$
\ket{\psi} = \sum_{i=0}^{2^n-1} \alpha_i \ket{i},
$$
where \\(\alpha_i\\) is a complex coefficient (also called amplitude) of the basis state \\(\ket{i}\\), and \\(i\\) is in its binary representation. When measuring the state of the system in the computational basis, the probability of observing the state \\(\ket{i}\\) as the output is \\(|\alpha_i|^2\\), and therefore \\(\sum_{i=0}^{2^n-1} |\alpha_i|^2 = 1\\). A quantum state of \\( n \\) qubits is then represented by the *state vector* 
$$
(\alpha_{0\dots 00},\alpha_{0\dots 01},...,\alpha_{1\dots 11})^\top,
$$
a unit vector of size \\( 2^n \\). For example, a 2-qubit state vector is written as
$$
(\alpha_{00},\alpha_{01},\alpha_{10},\alpha_{11})^\top.
$$

## Quantum Gates: Applying Operations to State Vectors
In quantum computing, computation is specified using quantum gates. Quantum gates are unitary operators that transform the state vector. The semantics of a \\(k\\)-qubit gate is specified by a \\(2^k \times 2^k\\) unitary complex matrix \\(U\\), and applying the gate to a quantum state \\(\ket{\psi}\\) results in a state denoted by the state vector \\(U \ket{\psi}\\).
If the quantum gate only operates on a part of qubits, we need to compute the tensor product before performing the matrix multiplication. For example, when applying the single-qubit gate 
$$
U_1(\theta) = \begin{pmatrix}
1 & 0 \\
0 & e^{i\theta}
\end{pmatrix}
$$
to the first qubit (the less significant bit in the state index) of a 2-qubit state, the computation becomes
$$
(U_1(\theta) \otimes I) \ket{\psi} = \begin{pmatrix}
1 & 0 & 0 & 0 \\
0 & e^{i\theta} & 0 & 0 \\
0 & 0 & 1 & 0 \\
0 & 0 & 0 & e^{i\theta}
\end{pmatrix}
\begin{pmatrix}
\alpha_{00}\\
\alpha_{01}\\
\alpha_{10}\\
\alpha_{11}
\end{pmatrix}.
$$

You may have realized that we don't actually have to explicitly compute the tensor product -- we can compute two \\(2\times 2\\) matrix-vector multiplications for the \\((\alpha_{00}, \alpha_{01})^\top\\) and \\((\alpha_{10}, \alpha_{11})^\top\\) parts in parallel. And yes, each \\(k\\)-qubit gate only requires \\(2^{n-k}\\) copies of \\(2^k \times 2^k \\) parallel matrix-vector multiplications.

State-vector simulation simply computes these matrix-vector multiplications on classical machines. Given such high parallelism (quantum gates are typically either single-qubit or two-qubit), it is natural to use GPUs, or more precisely, distributed GPUs for state-vector simulation when the exponential-sized state vector exceeds the memory limit of a single GPU.

# Setup
## Architectural Model
We assume a multi-node GPU architecture with \\(2^G\\) computation nodes. We present two variants of computation nodes: the first one is each node contains \\(2^R\\) GPUs, and each GPU can store \\(2^L\\) amplitudes (complex numbers), and the second one is each node contains some GPUs and a CPU with DRAM that can store \\(2^{L+R}\\) amplitudes. For simplicity, let's focus on the first variant first, where we can store the entire state vector of size
$$
2^n = 2^{G+R+L}
$$
on the GPUs.
We can associate the parameters with the qubits: suppose there are \\(G\\) global qubits, \\(R\\) regional qubits, and \\(L\\) local qubits, and we can simulate quantum circuits of \\(n = L + R + G\\) qubits. If there are fewer qubits (\\(n\\) is smaller), we can set \\(G = n - L - R\\) and use fewer GPU nodes.



