+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "Atlas: Hierarchical Partitioning for Quantum Circuit Simulation on GPUs"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2024-12-19

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


# TL; DR
- The workload of state-vector quantum circuit simulation is massively parallel. Most quantum gates multiply one small matrix to many vectors, and the workload is balanced.
- Challenge: the state vector is too large to be stored on one GPU, and the communication cost is very high. We want to keep the computation local.
- Atlas, using a hierarchical partitioning approach consisting of circuit staging and kernelization (i.e., partitioning the circuit into stages and then into GPU kernels), outperforms state-of-the-art distributed GPU simulators by more than \\(2\times\\).
- In circuit staging, an ILP algorithm minimizes the number of stages to minimize communication cost.
- In circuit kernelization, a DP algorithm outperforms previous greedy approaches by allowing for more gate reorderings.
- Both circuit staging and circuit kernelization played an important role in improving the performance.

# Background: Quantum Circuit Simulation

## Introduction
In the current Noisy Intermediate-Scale Quantum (NISQ) era, quantum computers are a scarce resource, and they suffer from decoherence and lack of error correction. Therefore, there is significant interest in quantum circuit simulation which enables performing robust quantum computation on classical parallel machine, and helps develop and debug quantum algorithms.

There are many methods to simulate quantum circuits. This blog post focuses on the *state-vector* (Schrödinger style) simulation, the most general, straightforward, and well-studied approach. Some other techniques for noise-free accurate quantum circuit simulation include:

- Feynman-path simulation, which is good for sparse circuits;
- Tensor network simulation, which is good for circuits with low entanglement;
- Stabilizer simulation, which is good for Clifford circuits.

These methods are usually used for circuits with certain structures, or circuits with too many qubits (> 40) that are beyond the capability of state-vector simulation. For general circuits with good "quantumness" (hard to simulate using a classical computer), state-vector simulation is usually the most efficient approach. Our work aims to make it even more efficient.

## Quantum State and State Vector
State-vector simulation features a direct representation of the quantum state. The state \\(\ket{\psi}\\) of an \\(n\\)-qubit quantum circuit can be represented by a superposition of its *basis states* denoted \\(\ket{0\dots 00}\\), \\(\ket{0\dots 01}\\), ..., \\(\ket{1\dots 11}\\), written as
$$
\ket{\psi} = \sum\_{i=0}^{2^n-1} \alpha\_i \ket{i},
$$
where \\(\alpha\_i\\) is a complex coefficient (also called amplitude) of the basis state \\(\ket{i}\\), and \\(i\\) is in its binary representation. When measuring the state of the system in the computational basis, the probability of observing the state \\(\ket{i}\\) as the output is \\(|\alpha\_i|^2\\), and therefore \\(\sum\_{i=0}^{2^n-1} |\alpha\_i|^2 = 1\\). A quantum state of \\( n \\) qubits is then represented by the *state vector* 
$$
(\alpha\_{0\dots 00},\alpha\_{0\dots 01},...,\alpha\_{1\dots 11})^\top,
$$
a unit vector of size \\( 2^n \\). For example, a 2-qubit state vector is written as
$$
(\alpha\_{00},\alpha\_{01},\alpha\_{10},\alpha\_{11})^\top.
$$

## Quantum Gates: Applying Operations to State Vectors
In quantum computing, computation is specified using quantum gates. Quantum gates are unitary operators that transform the state vector. The semantics of a \\(k\\)-qubit gate is specified by a \\(2^k \times 2^k\\) unitary complex matrix \\(U\\), and applying the gate to a quantum state \\(\ket{\psi}\\) results in a state denoted by the state vector \\(U \ket{\psi}\\).
If the quantum gate only operates on a part of qubits, we need to compute the tensor product before performing the matrix multiplication. For example, when applying the single-qubit gate 
$$
U\_1(\theta) = \begin{pmatrix}
1 & 0 \\\\
0 & e^{i\theta}
\end{pmatrix}
$$
to the first qubit (the less significant bit in the state index) of a 2-qubit state, the computation becomes
$$
(U\_1(\theta) \otimes I) \ket{\psi} = \begin{pmatrix}
1 & 0 & 0 & 0 \\\\
0 & e^{i\theta} & 0 & 0 \\\\
0 & 0 & 1 & 0 \\\\
0 & 0 & 0 & e^{i\theta}
\end{pmatrix}
\begin{pmatrix}
\alpha\_{00}\\\\
\alpha\_{01}\\\\
\alpha\_{10}\\\\
\alpha\_{11}
\end{pmatrix}.
$$

You may have realized that we don't actually have to explicitly compute the tensor product -- we can compute two \\(2\times 2\\) matrix-vector multiplications for the \\((\alpha\_{00}, \alpha\_{01})^\top\\) and \\((\alpha\_{10}, \alpha\_{11})^\top\\) parts in parallel. And yes, each \\(k\\)-qubit gate only requires \\(2^{n-k}\\) copies of \\(2^k \times 2^k \\) parallel matrix-vector multiplications.

State-vector simulation simply computes these matrix-vector multiplications on classical machines. Given such high parallelism (quantum gates are typically either single-qubit or two-qubit), it is natural to use GPUs, or more precisely, distributed GPUs for state-vector simulation when the exponential-sized state vector exceeds the memory limit of a single GPU.

Using distributed GPUs, however, inevitably incurs a high communication cost. In the following section, let's go through the setup of quantum circuit simulation on distributed GPUs and the causes of communications.

# Setup
## Architectural Model
We assume a multi-node GPU architecture with \\(2^G\\) computation nodes. We present two variants of computation nodes: the first one is each node contains \\(2^R\\) GPUs, and each GPU can store \\(2^L\\) amplitudes (complex numbers), and the second one is each node contains some GPUs and a CPU with DRAM that can store \\(2^{L+R}\\) amplitudes. For simplicity, let's focus on the first variant first, where we can store the entire state vector of size
$$
2^n = 2^{G+R+L}
$$
on the GPUs. We will discuss the DRAM offloading variant [at the end of this blog post](#dram-offloading).

## Local, Regional, and Global Qubits
The reason why the number of computation nodes \\(2^G\\), number of GPUs per node \\(2^R\\), and the GPU memory size \\(2^L\\) are all powers of two is that we can then associate the parameters with the qubits: suppose there are \\(G\\) global qubits, \\(R\\) regional qubits, and \\(L\\) local qubits. We can simulate quantum circuits of \\(n = L + R + G\\) qubits. If there are fewer qubits (\\(n\\) is smaller), we can set \\(G = n - L - R\\), and use fewer GPU nodes.

The following figure shows an example data layout of a state vector of 5 qubits on 2 nodes with 2 GPUs in each node. Suppose the qubits are indexed \\(q\_4 q\_3 q\_2 q\_1 q\_0 \\) in the state vector indices at the bottom of the figure. There is \\(G = 1\\) global qubit \\(q\_4\\), \\(R = 1\\) regional qubit \\(q\_3\\), and \\(L = 3\\) local qubits \\(q\_2, q\_1, q\_0\\). Node 0 stores the shards where the global qubit \\(q\_4 = \ket{0}\\), and GPU 0 stores the shard where the global qubit \\(q\_4\\) and the regional qubit \\(q\_3\\) are both \\(\ket{0}\\).

![Example data layout: The state vector consists of 32 entries from 00000 to 11111. Each GPU stores 8 amplitudes, and GPU 0 stores 00000 to 00111. The orange curves on the left show the pattern of simulating a CNOT gate on q1 and q0.](./data-layout-and-intra-gpu-comm.png)

## Simulating Quantum Gates on GPUs
### "Local" Gates
To simulate a quantum gate operating only on local qubits, we only need intra-GPU communication. For example, let's see how to simulate the CNOT gate highlighted in yellow in the figure below. CNOT, or controlled-NOT gate, has a control qubit (denoted by the small circle) and a target qubit (denoted by the large circle with a plus sign in it). It corresponds to the matrix
$$
CNOT = \begin{pmatrix}
1 & 0 & 0 & 0 \\\\
0 & 1 & 0 & 0 \\\\
0 & 0 & 0 & 1 \\\\
0 & 0 & 1 & 0
\end{pmatrix}.
$$
The gate does nothing when the control qubit is \\(\ket{0}\\), or applies the NOT operation (flipping \\(\ket{0}\\) to \\(\ket{1}\\), and \\(\ket{1}\\) to \\(\ket{0}\\)) to the target qubit when the control qubit is \\(\ket{1}\\). In the following circuit, the control qubit is \\(q\_1\\), and the target qubit is \\(q\_0\\). So, executing this gate is equivalent to swapping the amplitudes of \\(q\_0 = \ket{0}\\) and \\(q\_0 = \ket{1}\\) when \\(q\_1 = \ket{1}\\). The pattern of these swaps is shown in the orange curves on the left of the figure above. There is only intra-GPU communication when we execute this CNOT gate, and this property holds for any gate operating entirely on local qubits.

![An example quantum circuit with 5 qubits. q0, q1, q2 are local qubits. There is a CNOT gate with q1 being the control qubit and q0 being the target qubit highlighted in yellow, and a CNOT gate with q3 being the control qubit and q2 being the target qubit highlighted in blue.](./circuit-example.png)

### Do Not Execute "Non-Local" Gates
If a gate operates on non-local qubits, things become different. For example, the Hadamard gate on \\(q\_4\\), denoted by the letter H, would multiply a \\(2\times 2\\) matrix to each of the 16 vectors in
$$
\binom{\alpha\_{00000}}{\alpha\_{10000}}, \binom{\alpha\_{00001}}{\alpha\_{10001}}, \dots, \binom{\alpha\_{01111}}{\alpha\_{11111}}
$$
for the state vector \\((\alpha\_{00000}, \dots, \alpha\_{11111})^\top\\). This incurs fine-grained inter-GPU (and even inter-node because \\(q\_4\\) is a global qubit) communication at each and every entry of the state vector. This is very expensive, and we want to avoid executing such global gates by choosing the local qubit set carefully. In fact, it would be better to partition the circuit into stages, with a different local qubit set for each stage, so that all gates only operate on local qubits in each stage, and communication only happens between stages.

#### Exception: Insular Qubits
In fact, not all "non-local" gates are expensive. We call the non-local qubits in a gate that can be executed efficiently *insular qubits*. Insular qubits include the following two cases:

- For a single-qubit gate, the qubit is insular if the unitary matrix of the gate is diagonal or anti-diagonal.
- For a multi-qubit controlled gate, control qubits are insular.

For example, the last CNOT gate highlighted in blue in the figure above has a non-local control qubit \\(q\_3\\) and a local target qubit \\(q\_2\\). We can execute this gate efficiently by sending different instructions to different GPUs. Since the control qubit is non-local, we know if it is \\(\ket{0}\\) or \\(\ket{1}\\) from the GPU number. We can then lower the CNOT gate into a NOT gate when \\(q\_3 = \ket{1}\\) on GPUs 1 and 3, and do nothing when \\(q\_3 = \ket{0}\\) on GPUs 0 and 2.

This property allows Atlas to only consider the non-insular qubits of quantum gates when mapping qubits.

Putting these together, an algorithm seems ready to come out: iteratively execute as many local gates as possible that do not require inter-GPU communication, and then shard the state vector (remap the qubits) to make sure the next group of gates does not require inter-GPU communication. In this way, the communication cost is largely reduced. The following section introduces the entire picture of Atlas.

# Hierarchical Partitioning Overview

![Overview](./overview.png)


This figure shows an example application of circuit partitioning and execution. We stage the circuit so that (non-insular) qubits of each gate map to local qubits (i.e., green lines in each stage). The notation \\(q\_i[p\_j]\\) indicates that the \\(i\\)-th logical qubit maps to the \\(j\\)-th physical qubit (data layout). We then partition the gates of each stage into kernels for data parallelism. After partitioning into kernels, we execute the kernels on each GPU. Each GPU executes a shard of the state vector. Between each stage, we shard the state vector again via all-to-all communication between GPU pairs.

# Circuit Staging

Previous works relied on greedy heuristics for circuit staging, but we realize that the communication cost is so high that it’s worthwhile to use a provable algorithm for optimal circuit staging. Here is the problem formulation: given parameters \\(L, R, G\\), partition the circuit into stages to minimize the total communication cost such that each stage has \\(L\\) local qubits, \\(R\\) regional qubits, and \\G\\)global qubits, subject to the constraint that all non-insular qubits of all gates only operate on local qubits.

Because the sharding operation to remap the state vector with a different local qubit set is very expensive, and it is implemented by qubit swaps (the running time is positively correlated with the number of qubit pairs to be swapped), we optimize for the following objective:
$$
\sum\_{i=1}^{s-1} \left(\left|\mathcal{Q}\_i^{local} \setminus \mathcal{Q}\_{i-1}^{local}\right| + c \cdot \left|\mathcal{Q}\_i^{global} \setminus \mathcal{Q}\_{i-1}^{global}\right|\right).
$$
where \\(s\\) is the total number of stages, \\(c\\) is a pre-set inter-node communication cost factor (we use 3 in our evaluation), \\(\mathcal{Q}\_i^{local}\\) is the local qubit set of stage \\(i\\), and \\(\mathcal{Q}\_i^{global}\\) is the global qubit set of stage \\(i\\). \\(|\mathcal{Q}\_i^{local} \setminus \mathcal{Q}\_{i-1}^{local}|\\) is the number of local qubits that need to be updated, approximating the inter-GPU communication cost; \\(|\mathcal{Q}\_i^{global} \setminus \mathcal{Q}\_{i-1}^{global}| \\) is the number of global qubits that need to be updated, approximating the extra inter-node communication cost.

We design a binary Integer Linear Programming (ILP) algorithm to discover a staging strategy that minimizes the total communication cost. We loop over \\(s\\) from \\(1, 2 \dots\\), to try to solve the ILP for \\(s\\) stages. The core variables in the ILP algorithms are:

- \\(A\_{q,k}\in \{0,1\}\\): If the qubit \\(q\\) is local at the stage \\(k\\);
- \\(B\_{q,k}\in \{0,1\}\\): If the qubit \\(q\\) is global at the stage \\(k\\);
- \\(F\_{g,k}\in \{0,1\}\\): If the gate \\(g\\) is executed by the end of stage \\(k\\).

Using some ancillary variables, we can formulate the objective and constraints in the ILP.

In conclusion, on top of the minimum number of stages, the ILP minimizes the total communication cost.

# Circuit Kernelization

Now that we've partitioned the circuit into stages, let's execute each stage in GPU kernels. A straightforward way to execute gates is to create one kernel for each gate, but this incurs a high kernel launch overhead. A natural way to improve the performance is through kernel fusion, but it may amplify the computation exponentially. For example, if we fuse single-qubit gates on \\(k\\) qubits together, the matrix size becomes \\(2^k \times 2^k\\). Compared to \\(k\\) times of \\(2 \times 2 \\) matrix multiplying to \\(2^{n-1}\\) vectors of size \\(2\\) each, multiplying a single \\(2^k \times 2^k\\) matrix to \\(2^{n-k}\\) vectors of size \\(2^k\\) each would increase the computation by \\(2^{k-1} / k \\) times. Note that the computation workload is tiny, so this is not to say that we should not perform kernel fusion -- fusing 4-5 qubits is beneficial because it reduces kernel launch overhead, but fusing 20 qubits, for example, is not favorable.

Another way to improve the performance is to load the state vector into the GPU shared memory in batches, and then execute quantum gates sequentially in the shared memory. This is efficient for each gate, but it pays an overhead for loading and storing the state vector, and can only execute gates on a few qubits depending on the shared memory size.

We propose a Dynamic Programming (DP) algorithm for circuit kernelization. Given a cost function for kernels and a circuit sequence \\(\mathcal{C}\\) in a stage, we would like to partition \\(\mathcal{C}\\) into kernels \\(\mathcal{K}\_0, \dots, \mathcal{K}\_{b-1}\\) that minimizes the total execution cost
$$
\sum\_{i=0}^{b-1}Cost(\mathcal{K}\_i).
$$

To achieve the best kernelization result, we would like to allow for gate reordering in the sequence. The DP state \\(DP[i, \kappa]\\) represents an ordered kernel set \\(\kappa\\) for the first \\(i\\) gates in the gate sequence. However, we cannot partition the gates arbitrarily. The following figure shows an infeasible kernel schedule because the two blue dotted kernels are not "convex".

![Kernel examples. The two green dashed kernels satisfy the constraints. The two blue dotted kernels do not satisfy the constraints and thus are not considered by the DP algorithm.](./kernel-constraint.png)

To allow for gate reordering while not introducing infeasible kernel schedules, we present the following two constraints for the kernels to be considered by the algorithm:

- Weak convexity: \\(\forall j\_1 < j\_2 < j\_3\\), if \\(\mathcal{C}[j\_1] \in \mathcal{K}, \mathcal{C}[j\_2] \notin \mathcal{K}, \mathcal{C}[j\_3] \in \mathcal{K}\\), then \\(Qubits(\mathcal{C}[j\_1])\cap Qubits(\mathcal{C}[j\_2]) \cap Qubits(\mathcal{C}[j\_3]) = \emptyset\\).  Informally, weak convexity requires that for any three gates \\(\mathcal{C}[j\_1], \mathcal{C}[j\_2], \mathcal{C}[j\_3]\\), if only the middle gate is not in the kernel, then they cannot share a qubit.
- Monotonicity: If we decide to exclude a gate from \\(\mathcal{K}\\) while it shares a qubit with \\(\mathcal{K}\\), then we fix the qubit set of \\(\mathcal{K}\\) from that gate on. 

In the figure above, the blue dotted kernel on the left violates weak convexity because \\(\mathcal{C}[1]\\), \\(\mathcal{C}[2]\\) and \\(\mathcal{C}[4]\\) share \\(q\_2\\), and only \\(\mathcal{C}[2]\\) is not in the kernel. If we allow this kernel to be considered, it will be mutually dependent with the kernel containing \\(\mathcal{C}[2]\\), yielding no feasible results. The blue dotted kernel on the right does not violate weak convexity, but it violates monotonicity. \\(\mathcal{C}[7]\\) is excluded from the kernel while sharing the qubit \\(q\_1\\) with the kernel, so the qubit set of the kernel should be fixed to \\(\{q\_0, q\_1\}\\). So it cannot include \\(\mathcal{C}[9]\\). In fact, including \\(\mathcal{C}[9]\\) in this kernel causes mutual dependency with the kernel \\(\{\mathcal{C}[7],\mathcal{C}[8]\}\\).

These two constraints impose a low cost in implementation (in terms of the running time of the kernelization algorithm) while allowing for some gates to be reordered in the sequence. If you are interested in the implementation details of the DP algorithm, please check out [our paper](https://arxiv.org/pdf/2408.09055) :)

# Comparing with Previous Works
We compare our work Atlas with previous distributed GPU simulators HyQuas, cuQuantum, and Qiskit. They all store the entire state vector on GPUs. The following figure shows a weak scaling experiment on the circuit family of QFT, and all circuits in our benchmark of 11 quantum circuit families exhibit a similar pattern. 

![Weak scaling of Atlas, HyQuas, cuQuantum, and Qiskit with 28 local qubits as the number of global qubits increases from 0 (on 1 GPU) to 8 (on 256 GPUs) on the QFT circuits. Qiskit is slow and usually does not fit into our charts.](./qft-perf.svg) 

HyQuas performs well when the number of GPUs is small, but it does not scale well when the number of GPUs is large. HyQuas also partition the circuit into kernels, but it uses a greedy approach: it packs gates into kernels of 4-7 qubits or uses a shared-memory kernel, greedily choosing the one with the best arithmetic density each time. cuQuantum, developed by NVIDIA, scales better than HyQuas, but it is slower and not as scalable as Atlas. cuQuantum uses a tailored function "custatevecMultiDeviceIndexBitSwaps" to minimize communication, but it does not focus on circuit kernelization: cuQuantum simply packs gates up to 4 or 5 qubits depending on the GPU model.

In summary, circuit staging and kernelization are both important.

On a benchmark of 99 circuits, Atlas is \\(4\times\\) on average faster than HyQuas, \\(3.2\times\\) on average faster than cuQuantum, and \\(286\times\\) on average faster than Qiskit. 


## DRAM Offloading
In addition to improving quantum circuit simulation performance, another key advantage of Atlas over existing systems is its ability to scale to larger circuits beyond the GPU memory capacity. Recall that we assumed that each computation node has \\(2^R\\) GPUs [before](#architectural-model). Instead, suppose we do not have that many GPUs, but only some GPUs and a CPU with DRAM that can store \\(2^{L+R}\\) amplitudes (complex numbers). In each stage, we will then have to run \\(2^R\\) shards of the state vector serially on one GPU by loading the shard from the DRAM, execute the kernels, and then store the shard back to DRAM each time (or let each GPU run \\(2^R / p\\) shards serially if we have \\(p\\) GPUs).

We compare Atlas with QDAO which is another GPU simulator using DRAM offloading to support larger circuits. The figure below (note that the \\(y\\)-axis is in log-scale) shows that Atlas runs \\(61\times\\) faster than QDAO on average on the QFT circuits with 28-32 total qubits on a single GPU with 28 local qubits, and scales better.

![Atlas outperforms QDAO by 61 times on average. Log-scale simulation time (single GPU) with DRAM offloading for QFT circuits.](./scalability-qdao.svg)

## Circuit Staging & Kernelization

We have also done evaluations on the circuit staging and kernelization algorithms, and they both achieve a significant improvement over prior approaches.

For circuit staging, we compare with SnuQS, which greedily selects the qubits with more gates operating on non-local gates in the current stage to form the next stage, and uses the number of total gates as a tiebreaker. Other works did not describe how the heuristics were implemented. The following figure shows the geometric mean number of stages for all 11 circuits with 31 qubits in our benchmark suite. Our circuit staging algorithm is guaranteed to return the minimum number of stages, and it always outperforms SnuQS' approach. 

![Number of stages, Atlas versus SnuQS: The geometric mean over all our benchmark circuits with 31 qubits.](./ilp-plot-31.svg)

For circuit kernelization, we compare with a baseline that greedily packs gates into fusion kernels of up to 5 qubits, the most cost-efficient kernel size in the cost function used in our experiment setting. Each circuit family exhibits a pattern, so we take the geometric mean of the cost for 9 circuits with the number of qubits from 28 to 36 for each circuit family. The following figure shows that the greedy baseline performs well in dj and qsvm circuits, but it does not generalize to other circuits. Our kernelization algorithm is able to exploit the pattern for each circuit and find a low-cost kernel sequence accordingly.

![Kernelization effectiveness: The relative geometric mean cost of KERNELIZE compared to greedy packing up to 5 qubits.](./dp-circuit-geomean-relative.svg)

# Conclusion

We have presented Atlas, an efficient and scalable Schrödinger-style distributed multi-GPU quantum circuit simulator. It uses a hierarchical partitioning approach with an ILP algorithm for circuit staging and a DP algorithm for kernelization, and significantly outperforms existing simulators.
