+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "Optimizing Million-Gate Quantum Circuits in Parallel"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2026-11-23

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Programming Languages", "Systems", "Theory"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
# Consider these similar to keywords specified for a research paper.
tags = ["quantum-computing", "circuit-optimization", "parallel-algorithms", "compilers"]

[extra]
author = {name = "Pengyu Liu", url = "https://www.pengyuliu.me/" }
# The committee specification is  a list of objects similar to the author.
committee = [
    {name = "Zhihao Jia", url = "https://www.cs.cmu.edu/~zhihaoj2/"},
    {name = "Ryan O'Donnell", url = "https://www.cs.cmu.edu/~odonnell/"},
    {name = "Zikun Li", url = "https://zikun-li.github.io/"}
]
+++

Imagine a compiler that needs fifteen hours to optimize a program. That would be impractical in a classical toolchain. For large *quantum circuits*, the programs of a quantum computer, such optimization times are common. VOQC ([Hietala et al., 2021](https://arxiv.org/abs/1912.02250)), the fastest optimizer for circuits this large prior to our work, spends almost fifteen hours on a half-million-gate circuit from Shor's factoring algorithm and does not finish a six-million-gate circuit for solving linear systems within a day. This problem will become more severe, because circuits for error-corrected machines are expected to have even more gates ([Preskill, 2025](https://arxiv.org/abs/2502.17368)) and existing optimizers cannot handle such circuits in a reasonable time.

This post describes POPQC, a parallel algorithm for optimizing quantum circuits, which my coauthors and I presented at SPAA 2025 ([paper](https://arxiv.org/abs/2506.13720), [code](https://github.com/UmutAcarLab/popqc)). POPQC optimizes the six-million-gate circuit in 35 seconds, a speedup of more than 2,400× over VOQC. On the circuits that VOQC finishes, POPQC maintains comparable optimization quality on average.

POPQC achieves these results by using local optimality and parallelism. Local optimality provides a precise guarantee on output quality and enables near-linear time. Parallelism further speeds up the execution and makes it scalable. We start with the quantum circuit model and why existing optimizers are slow. We then define local optimality, explain how POPQC achieves it in parallel, and examine its performance in practice.

# Quantum programs for computer scientists

A classical bit is 0 or 1, whereas a *qubit*'s state is a unit vector \\(\alpha|0\rangle + \beta|1\rangle\\). It combines two basis vectors, written \\(|0\rangle\\) and \\(|1\rangle\\), with complex *amplitudes* \\(\alpha\\) and \\(\beta\\). The state of \\(m\\) qubits is a unit vector of \\(2^m\\) amplitudes, one for each \\(m\\)-bit string.

A *quantum program* on \\(m\\) qubits starts from the all-zero state \\(|0\cdots0\rangle\\) and applies a *unitary map*, a length-preserving linear map, to produce a final state that encodes the answer. This map is a \\(2^m \times 2^m\\) matrix, which is exponentially large, so a program builds it from *gates*, small operations that each act on one or two qubits. We need four kinds of gates:

- The *X gate* \\(\mathrm{X}\_q\\) flips qubit \\(q\\), like a NOT gate.
- The *Hadamard gate* \\(\mathrm{H}\_q\\) turns \\(|0\rangle\\) to \\((|0\rangle+|1\rangle)/\sqrt{2}\\) and \\(|1\rangle\\) to \\((|0\rangle-|1\rangle)/\sqrt{2}\\).
- The *CNOT* (controlled NOT) gate \\(\mathrm{CNOT}\_{c,t}\\) flips its *target* qubit \\(t\\) if its *control* qubit \\(c\\) is 1.
- The *\\(\mathrm{R}\_z\\) rotation* \\(\mathrm{R}\_z(\theta)\\) rotates a qubit's phase by an angle \\(\theta\\), i.e. it maps \\(\alpha|0\rangle+\beta|1\rangle\\) to \\(\alpha |0\rangle+\beta e^{i\theta}|1\rangle\\).

A quantum program is a sequence of such gates, like a straight-line program with no loops or branches. We visualize a program as a quantum circuit, with one wire per qubit and time flowing left to right. Each gate is drawn on the wires of the qubits it acts on, in program order. The figure below shows a program with four gates on three qubits, \\(q\_0\\) to \\(q\_2\\), written as a sequence (top) and drawn as a circuit (bottom). From now on, we use "circuit" for both the program and its drawing.

![A program of four gates on three qubits, q0 to q2: H0, CNOT 0-1, X2, CNOT 2-1. Top: the program written as a sequence of gate names. Bottom: the same program drawn as a circuit, with one horizontal wire per qubit and an arrow showing time flowing left to right; each gate sits in its own shaded column, directly below its name. CNOT 0-1 has its control dot on q0 and its target circle on q1; CNOT 2-1 has its control on q2 and its target on q1. A legend says that a wire is a qubit and a box is a gate, and explains the H, X and CNOT symbols.](./program-circuit.png)

*A four-gate program written as a sequence (top) and drawn as a circuit (bottom), one gate per column.*

Two circuits are *equivalent* if they map every input state to the same output state, so replacing a contiguous piece with an equivalent sequence preserves the behavior of the whole circuit. This substitution is the basis of *circuit optimization*: finding an equivalent circuit with fewer gates to reduce runtime and error rate. For example, the nine-gate circuit at the top left of the next figure is equivalent to the five-gate circuit at its bottom left.

How does an optimizer find the smaller circuit? Like a classical peephole optimizer, it replaces a few neighboring gates with an equivalent sequence, using local rewrite rules such as those in panel (b) of the figure below. Some rules remove gates, and others rearrange them. Our example relies on the first rule in panel (b): if a CNOT has an H before it on one qubit and an H after it on the other, the two H gates can swap sides, provided the CNOT is reversed.

Rewrites also enable each other. Panel (a) of the figure below shows how our nine gates become five in three steps. In each row, the highlighted gates are the ones the next step rewrites.

![Panel (a), left: a nine-gate circuit on four qubit wires, q0 to q3, drawn as given and again after each of three rewrite steps, with the gates that the next step rewrites highlighted. Step 1 moves the H gates around CNOT 2-3 to its other sides and reverses it, still nine gates; step 2 does the same around CNOT 1-2, and the two H gates that meet on q2 cancel, leaving seven gates; step 3 does the same around CNOT 0-1, and the two H gates on q1 cancel, leaving the optimized five-gate circuit H3, CNOT 3-2, CNOT 2-1, H0, CNOT 1-0. Panel (b), right: local rewrite rules: H gates swapping sides across a CNOT while it is reversed, two H, X or CNOT gates canceling, two Rz rotations merging, and an X moving past a CNOT's target.](./rewrite-propagation.png)

*Our nine-gate circuit (top left) becomes an equivalent five-gate circuit (bottom left) in three steps. Each step uses a local rule like those on the right and sets up the next.*

**Step 1.** The rule turns \\(\mathrm{H}\_2\ \mathrm{CNOT}\_{2,3}\ \mathrm{H}\_3\\) into \\(\mathrm{H}\_3\ \mathrm{CNOT}\_{3,2}\ \mathrm{H}\_2\\). The circuit keeps nine gates, but an \\(\mathrm{H}\_2\\) now sits right before \\(\mathrm{CNOT}\_{1,2}\\).

**Step 2.** The rule applies to \\(\mathrm{CNOT}\_{1,2}\\), using the \\(\mathrm{H}\_1\\) from the start of the circuit and the \\(\mathrm{H}\_2\\) after the CNOT. The three gates between \\(\mathrm{H}\_1\\) and \\(\mathrm{CNOT}\_{1,2}\\) act on qubits 2 and 3, so \\(\mathrm{H}\_1\\) *commutes* with them: it can move past them without changing the circuit's behavior. The rule turns \\(\mathrm{H}\_1\ \mathrm{CNOT}\_{1,2}\ \mathrm{H}\_2\\) into \\(\mathrm{H}\_2\ \mathrm{CNOT}\_{2,1}\ \mathrm{H}\_1\\). The new \\(\mathrm{H}\_2\\) meets the one from step 1, and the two cancel, leaving seven gates.

**Step 3.** The \\(\mathrm{H}\_1\\) from step 2 now sits right before \\(\mathrm{CNOT}\_{0,1}\\), which has \\(\mathrm{H}\_0\\) after it. The rule applies once more, this time with the H before the CNOT on its target rather than its control: \\(\mathrm{H}\_1\ \mathrm{CNOT}\_{0,1}\ \mathrm{H}\_0\\) becomes \\(\mathrm{H}\_0\ \mathrm{CNOT}\_{1,0}\ \mathrm{H}\_1\\). The resulting \\(\mathrm{H}\_1\\) cancels the final \\(\mathrm{H}\_1\\), leaving five gates.

Each step involves three or four neighboring gates, yet the effect propagates across the whole circuit, from qubit 3 up to qubit 0. Step 1 removes no gates but enables the later reductions.

# Why not find the best circuit?

An ideal optimizer would return the smallest circuit equivalent to its input. But even deciding whether a circuit is approximately equivalent to doing nothing is *QMA-complete*, the quantum analogue of NP-complete ([Janzing, Wocjan, and Beth, 2005](https://arxiv.org/abs/quant-ph/0305050)). Finding the smallest equivalent circuit is at least as hard, so practical optimizers are heuristics.

*Rule-based* optimizers apply hand-designed rewrite rules in passes over the circuit. Examples are the optimizer of [Nam et al. (2018)](https://doi.org/10.1038/s41534-018-0072-4) and VOQC. In practice, they take quadratic time or more. *Search-based* optimizers such as Quartz ([Xu et al., 2022](https://doi.org/10.1145/3519939.3523433)) and Queso ([Xu et al., 2023](https://doi.org/10.1145/3591254)) search over rewrite sequences. They excel on small inputs but take exponential time. All of these optimizers run sequentially. Among existing optimizers, VOQC is the fastest at the circuit sizes we consider.

On our benchmarks, VOQC's running time is at least quadratic in the circuit size: doubling the circuit size makes VOQC four or more times slower. So even the fastest existing optimizer is not fast enough for large circuits.

![Log-log scatter plot of VOQC's optimization time against circuit size for the 32 benchmark circuits, colored by family. Times rise from 0.3 seconds on the smallest circuit to about 15 hours on Shor-16, climbing more steeply than a dotted quadratic guide line. Five circuits, between about one and six million gates, hit the 24-hour timeout and are drawn with upward arrows.](./voqc-scaling.png)

*VOQC's time grows faster than the square of circuit size, and 5 of 32 runs time out. Circuit names give family and qubit count.*

The optimizers we know of thus face three challenges:

1. They run sequentially.
2. Most take time that grows faster than circuit size.
3. Their heuristic outputs lack a quality guarantee.

In the following sections, we explain how we designed POPQC to handle all three challenges at once, with parallel execution, near-linear time, and a precise guarantee on output quality.

# Local optimality

Because global optimality is out of reach, POPQC uses a weaker notion, local optimality, which we introduced in earlier work ([Arora et al., 2025](https://arxiv.org/abs/2502.19526)). The definition builds on an existing optimizer, which we call the *oracle*: a classical program such as VOQC, used as a black box. Fix a segment length \\(\Omega\\), and call any run of \\(\Omega\\) consecutive gates an *\\(\Omega\\)-segment*. A circuit is *locally optimal* if the oracle cannot optimize any of its \\(\Omega\\)-segments, that is, it cannot return a smaller equivalent circuit for any of them:

$$|A| \le |\mathrm{oracle}(A)| \quad \text{for every } \Omega\text{-segment } A,$$

where \\(|A|\\) is the number of gates in \\(A\\). The condition must hold for every \\(\Omega\\)-segment at every starting position, so these segments overlap.

![A row of 12 gate cells, g1 to g12, with Omega equal to 4. Bars above the row mark every run of four consecutive gates, the Omega-segments. One segment, g5 to g8, is sent to a box labeled oracle, any existing optimizer such as VOQC, which cannot optimize it. A side note states the definition and that it is relative to the oracle, Omega and the gate order.](./local-optimality.png)

*Locally optimal: the oracle cannot optimize the Ω-segment at any offset.*

The guarantee is relative to the oracle, to \\(\Omega\\), and to the gate order. Gates on different qubits can be listed in either order, so two gates that could cancel may end up hundreds of gates apart. In practice, a modest \\(\Omega\\) is enough: with \\(\Omega = 200\\), POPQC matches VOQC's quality on most circuits, as the results below show.

# The trouble with boundaries

The definition of local optimality looks at one short segment at a time, and the oracle is slow on millions of gates but fast on a few hundred. It's natural to consider algorithms that work on short segments: each step takes a segment of length proportional to \\(\Omega\\) out of the circuit, calls the oracle on it, and writes the result back if it is smaller. For a fixed \\(\Omega\\), each call takes constant time, so the total cost depends on the number of calls. The question is how to organize the calls: which segments to optimize, in what order, and which calls can run at the same time.

The difficulty is that \\(\Omega\\)-segments overlap: optimizing one segment changes gates that also belong to its neighbors. This can create new opportunities there, and the resulting rewrites can propagate farther, as in our nine-gate example. Two simple approaches show the problem.

The first approach cuts the circuit into blocks, optimizes them in parallel, and glues the results together, but it does not guarantee local optimality. Consider the six-gate circuit \\(\mathrm{H}\_0\ \mathrm{CNOT}\_{0,1}\ \mathrm{X}\_1\ \mathrm{X}\_1\ \mathrm{CNOT}\_{0,1}\ \mathrm{H}\_0\\). The two X gates cancel, then the two CNOTs, then the two H gates, leaving nothing. But if a cut falls between the two \\(\mathrm{X}\_1\\) gates, the oracle cannot optimize either half, and all six gates survive (top of the figure below).

The second approach fixes the boundaries by sweeping from left to right over every starting position of an \\(\Omega\\)-segment, including overlapping ones. At each position, the sweep calls the oracle and accepts its output only if it reduces the gate count. Repeat these full sweeps until an entire sweep makes no improvement. A sweep with no accepted changes checks every \\(\Omega\\)-segment of an unchanged circuit, so the result is locally optimal. But the method can require quadratic *work*, the running time on one core, for fixed \\(\Omega\\), because each sweep over a circuit of \\(n\\) gates makes \\(O(n)\\) oracle calls and up to \\(O(n)\\) sweeps may be needed when each one removes only a few gates (bottom of the figure).

![Two panels. Top: the six-gate example circuit is cut into two three-gate blocks; the oracle cannot optimize either block, so the two X1 gates on either side of the cut survive and the result is not locally optimal. Bottom: four schematic sweeps over every starting position of an Omega-segment, including overlapping segments. Each cell represents an oracle call, not a disjoint circuit block. The first three sweeps find improvements; the fourth checks every position without accepting any change, so the algorithm stops. Most calls, shown as gray hatched cells, find no improvement.](./fixed-cuts.png)

*Fixed cuts miss cross-boundary rewrites. Full sweeps check every segment position, but repeatedly recheck segments that have not changed.*

We call an oracle call *successful* if it reduces the gate count of its segment, and *unsuccessful* otherwise. The local-optimality proof places two conditions on the oracle. It must be *well-behaved*: no \\(\Omega\\)-segment of its output can be improved by applying the oracle again. It must also return its input unchanged on unsuccessful calls, because POPQC keeps the original segment in that case.

Under these oracle conditions, each rewrite has local consequences even when a chain of rewrites propagates far. A rewrite changes only the gates it replaces, so every \\(\Omega\\)-segment that does not overlap the rewritten segment is unchanged. The rewritten segment itself is oracle output, so the oracle cannot improve any \\(\Omega\\)-segment inside it. New opportunities can appear only at the boundaries of the rewritten segment. POPQC therefore needs to remember only those places and can revisit distant ones in parallel.

# Fingers: remembering where to look again

POPQC marks the boundaries of each rewritten segment with *fingers*, positions between gates, and maintains one invariant:

> Every \\(\Omega\\)-segment that the oracle could still optimize contains a finger.

<p></p>

A finger marks a place where the oracle might still find an improvement, so POPQC does not need to look at an \\(\Omega\\)-segment without a finger again unless a later rewrite changes some of its gates. Once no fingers remain, the circuit is therefore locally optimal. POPQC starts with evenly spaced fingers, one every \\(\Omega\\) gates, so every \\(\Omega\\)-segment contains a finger and the invariant holds from the start. It proceeds in *rounds*:

```
POPQC(circuit C, oracle, segment length Ω):
  F ← a finger every Ω gates of C
  while F is not empty:                           // one round
    P ← fingers of F, pairwise ≥ 2Ω gates apart   // 1. select
    N ← ∅                                         //    new fingers
    in parallel, for each finger f in P:          // 2. optimize
      A  ← the 2Ω-segment centered on f
      A' ← oracle(A)
      if |A'| < |A|:                              // 3. update
        write A' back in place of A
        add a finger at each end of A' to N
    F ← (F − P) ∪ N                               // 4. merge
  return C
```

The *\\(2\Omega\\)-segment* of a finger consists of the \\(\Omega\\) gates on each side of it. The \\(2\Omega\\) spacing keeps the \\(2\Omega\\)-segments of the selected fingers disjoint, so the oracle calls run in parallel without locks. Every \\(\Omega\\)-segment that contains a selected finger lies inside that finger's \\(2\Omega\\)-segment, so one call checks all of these \\(\Omega\\)-segments. If the call is unsuccessful, the oracle conditions above guarantee that none of these \\(\Omega\\)-segments can be improved, and POPQC removes the finger. Otherwise, POPQC writes the smaller segment back and adds two new fingers at its ends. Inside a \\(2\Omega\\)-segment, the oracle may use rewrites that keep the gate count, like step 1 of our nine-gate example, but POPQC checks only whether the segment as a whole got smaller.

## A worked example

Here is the example from our paper, with \\(\Omega = 2\\) and eight gates in array slots 0 to 7. A finger at position \\(p\\) sits between slots \\(p-1\\) and \\(p\\). We start with only two fingers, at positions 2 and 6, which satisfies the invariant because no two adjacent gates simplify.

![Three views of an eight-slot gate array with Omega equal to 2, holding X2, H0, CNOT 1-2, X2, CNOT 0-2, CNOT 1-2, X0, CNOT 0-1. Round 1: fingers at positions 2 and 6 run with four-gate segments; the left segment loses its two X2 gates and finger 6 is removed. Round 2: finger 4 runs on a segment that skips the deleted slot 3, and the two CNOT 1-2 gates cancel. Afterwards four gates remain, and fingers at 0, 1 and 6 are removed in later rounds.](./fingers-example.png)

*Round 1 removes two X gates and adds boundary fingers; the segment around finger 4 then reveals the CNOT cancellation.*

**Round 1.** Fingers 2 and 6 are exactly \\(2\Omega = 4\\) gates apart, so both are selected. In the left segment, \\(\mathrm{X}\_2\ \mathrm{H}\_0\ \mathrm{CNOT}\_{1,2}\ \mathrm{X}\_2\\), the first \\(\mathrm{X}\_2\\) commutes past \\(\mathrm{H}\_0\\) (which acts on another qubit) and the CNOT (because X acts on its target). It then cancels the second \\(\mathrm{X}\_2\\). Slots 0 and 3 are marked deleted, and fingers 0 and 4, at the segment's ends, replace finger 2. The oracle cannot shrink the right segment, so finger 6 is removed.

**Round 2.** Fingers 0 and 4 are now two live (undeleted) gates apart, closer than \\(2\Omega\\), so only one can be selected. We select finger 4, because selecting finger 0 would only delay this call by a round. The selected finger's segment skips deleted slot 3: \\(\mathrm{H}\_0\ \mathrm{CNOT}\_{1,2}\ \mathrm{CNOT}\_{0,2}\ \mathrm{CNOT}\_{1,2}\\). CNOTs sharing a target can be swapped, so the two \\(\mathrm{CNOT}\_{1,2}\\) cancel. Slots 2 and 5 are deleted, fingers 1 and 6 replace finger 4, and finger 0 remains for a later round. Rounds 3 to 5 remove the remaining fingers, leaving an equivalent circuit of four gates.

## Choosing fingers in parallel

In round 2 of the example, we selected a finger by hand. In general, step 1 must select fingers that are pairwise at least \\(2\Omega\\) gates apart, and it must do so in parallel. POPQC divides the live gates into consecutive groups of \\(2\Omega\\) and picks the first finger in each group that contains one. Picks from even-numbered groups have a whole odd-numbered group between them, so they are at least \\(2\Omega\\) gates apart. The same holds for odd-numbered groups, and POPQC selects the larger of the two sets.

A finger's group follows from the number of live gates before it, found with an index-tree query described next. Selection therefore uses a parallel map and filter. A group holds at most \\(2\Omega\\) fingers, so \\(|F|\\) fingers yield at least \\(|F|/(2\Omega)\\) picks. The larger set has at least half of them, a \\(1/(4\Omega)\\) fraction of all fingers, which ensures that each round has enough parallelism.

![24 live gates split into six groups of four gates (2 Omega), alternately even and odd, with nine fingers. The first finger of each group is picked: fingers 2, 9 and 17 from the even groups and 5 and 22 from the odd groups. The larger, even set runs; its three four-gate segments do not overlap, and the other six fingers wait for a later round.](./select-fingers.png)

*Picks from alternate groups of 2Ω gates are far enough apart that their 2Ω-segments cannot overlap.*

# Deleting gates without moving them

POPQC needs a circuit representation that supports both edits and parallel access. A linked list makes deletion easy, but locating gates by position requires following pointers. An array supports direct access, but deleting gates and shifting the remaining entries is expensive. Even if a round batches all its deletions into one compaction, that compaction costs \\(O(n)\\), and over many rounds this can add up to quadratic overhead.

POPQC therefore keeps the array and leaves a *tombstone*, a marker for an empty slot, wherever it deletes a gate. This avoids shifting entries, but array positions no longer count live gates. Selection needs the number of live gates before each finger, and fetching a \\(2\Omega\\)-segment needs the \\(\Omega\\)-th live gate on either side. Finding them by scanning the array can be slow when tombstones accumulate.

To support these queries, POPQC adds an *index tree*, a complete binary tree over the array slots. Like a Fenwick tree, it stores counts: each leaf holds 1 for a gate and 0 for a tombstone, and each internal node stores the number of live gates below it. Two queries take \\(O(\log n)\\) time:

- `before(i)` counts the live gates before slot \\(i\\) by walking up from leaf \\(i\\), adding left siblings' counts.
- `get(k)` finds the \\(k\\)-th live gate by walking down from the root. At each node, it goes left if the left child holds at least \\(k\\) gates; otherwise, it goes right and subtracts the left child's count from \\(k\\).

Fetching a \\(2\Omega\\)-segment takes one `before` for the finger's rank and one `get` per gate. Each round's write-backs form one parallel batch: \\(\ell\\) updates take \\(O(\ell \log n)\\) work and, with enough cores, \\(O(\log n)\\) time.

![Two panels. Top: the index tree over the eight slots of the example after round 1, with leaves 0, 1, 1, 0, 1, 1, 1, 1 and a root of 6; a red path shows get(3) walking down to slot 4, which holds CNOT 0-2, and a green mark shows the single left sibling that before(4) adds, giving 2. Bottom: round 2 deletes slots 2 and 5, and only the nodes on their paths to the root change, so the root drops to 4.](./index-tree.png)

*get(3) walks down, before(4) walks up, and deletions update only their paths to the root.*

# Optimality and efficiency guarantees

Under the oracle conditions above, each round preserves the invariant. An unsuccessful call leaves no improvable \\(\Omega\\)-segment inside its \\(2\Omega\\)-segment. After a successful call, any newly improvable \\(\Omega\\)-segment crosses a boundary of the rewritten segment, so it contains a new finger. It remains to show that the process terminates and to bound its work and its *span*, the running time with unlimited cores.

A successful call removes one finger and adds two, but it also removes at least one gate. We track both changes with the *potential function*

$$\Phi = |F| + 2|C|,$$

where \\(F\\) is the set of fingers and \\(C\\) the circuit, so \\(|C|\\) counts live gates. An unsuccessful call removes its finger, so \\(\Phi\\) drops by 1. A successful call removes at least one gate (\\(-2\\)) and increases the number of fingers by one (\\(+1\\)), so \\(\Phi\\) drops by at least 1. It starts at about \\(n/\Omega + 2n\\) and never goes negative, so POPQC makes \\(O(n)\\) oracle calls.

**Work and span.** Let \\(W\\) and \\(S\\) be the work and span of one oracle call, and \\(r\\) the number of rounds. POPQC has

$$\begin{gathered}\text{work} = O\big(n(\Omega \log n + W)\big), \\\\ \text{span} = O\big(r(\log n + S)\big).\end{gathered}$$

Each of the \\(O(n)\\) calls fetches its \\(2\Omega\\)-segment with \\(O(\Omega)\\) index-tree queries. Selection examines every waiting finger in every round. Because each round runs at least a \\(1/(4\Omega)\\) fraction of them and there are \\(O(n)\\) calls in total, all rounds together examine \\(O(\Omega n)\\) fingers, at \\(O(\log n)\\) each. Each round adds \\(O(\log n + S)\\) to the span. For constant \\(\Omega\\), this gives \\(O(n \log n)\\) work, a logarithmic factor above the linear time needed to read the circuit, and \\(O(r \log n)\\) span.

The span depends on the number of rounds, which is hard to predict and can be as high as \\(n\\) in the worst case. As the experiments in the next section show, the number of rounds is much smaller in practice.

# Does it work in practice?

POPQC is written in Rust with the Rayon fork-join library and calls the oracle as a separate program, so oracles are easy to swap. We run it with VOQC and \\(\Omega = 200\\) on a 64-core AMD EPYC 7763 with 256 GB of memory. The baseline is sequential VOQC with a 24-hour timeout. The 32 benchmarks come from the PennyLane, Qiskit, and NWQBench suites and cover eight families at four sizes each, from 5,796 to 5,954,308 gates. The families include Shor's factoring, Grover's search, and HHL for linear systems.

## Seconds instead of hours

![Log-log plot of optimization time against circuit size for all 32 circuits. Gray points for sequential VOQC rise from under a second to many hours, with five timeouts drawn at the 24-hour line; blue points for POPQC on 64 cores stay between about half a second and 35 seconds. Callouts mark HHL-13, over 24 hours for VOQC versus 35.1 seconds for POPQC, and HHL-7, where POPQC takes 0.8 seconds and VOQC 0.3.](./runtime-vs-size.png)

*On 64 cores POPQC finishes every circuit within 35.1 seconds; VOQC times out on five.*

The arithmetic mean of the 32 per-circuit speedups is at least 1,944×, counting each VOQC timeout as 24 hours. On the smallest circuit, HHL-7, POPQC is slower, 0.8 seconds versus 0.3, because fixed overheads dominate.

![Stacked bars on a log scale for the three longest VOQC runs that finished, splitting POPQC's speedup over VOQC into locality, VOQC's time over POPQC's one-core time, and parallelism, POPQC's one-core time over its 64-core time. Shor-16: 394 times 33, about 13,111. HHL-11: 217 times 26, about 5,601. BWT-21: 100 times 27, about 2,713.](./speedup-breakdown.png)

*On the three longest VOQC runs that finished, locality gives 100× to 394× and 64 cores add 26× to 33×.*

Single-core runs separate the two sources of speedup, locality and parallelism. Most of the gain comes from locality: calling VOQC a linear number of times on small segments beats running its superlinear passes on the whole circuit. Single-core POPQC is at least 73× faster than VOQC on average over the 32 circuits, again counting each timeout as 24 hours.

## Scaling with cores

To measure the gain from parallelism alone, we use *self-speedup*: POPQC's time on one core divided by its time on more cores.

![Line plot of self-speedup against the number of cores, from 1 to 64, for the largest circuit of each of the eight families, with a dashed line for ideal speedup. At 64 cores the curves reach 38.2 for HHL, 35.7 for Sqrt, 33.7 for BWT, 33.2 for Shor, 28.4 for StateVec, 22.9 for Grover, 18.6 for BoolSat and 9.4 for VQE, whose curve peaks at 32 cores.](./self-speedup-threads.png)

*Six of eight families reach a self-speedup of 20× or more on their largest circuit.*

The 32 circuits need between 17 and 130 rounds. HHL's largest circuit is 1,027 times larger than its smallest, yet it needs 63 rounds instead of 40. This modest increase suggests that the round count may stay small on larger circuits, giving a small span.

BoolSat and VQE stay below 20× for different reasons. BoolSat needs the most rounds, and rounds must run one after another. VQE's largest circuit is the smallest in the figure, about 100,000 gates, so each round has too little work to keep 64 cores busy. Within every family, self-speedup grows with circuit size, so parallelism helps most on large circuits.

## Quality is comparable

![Scatter plot of the percentage of gates removed by POPQC against the percentage removed by VOQC, for the 27 circuits where VOQC finished, with a dashed diagonal where both are equal. Most points lie on the diagonal. The three HHL circuits sit 14.4 to 14.8 points above it, POPQC better, and the three Sqrt circuits 0.9 to 3.4 points below it. Averages over the 27 circuits: VOQC 48.94 percent, POPQC 50.33 percent.](./quality.png)

*POPQC matches VOQC on most circuits, beats it by about 15 points on HHL, and falls up to 3.4 points short on Sqrt.*

On the 27 circuits VOQC finished, POPQC is within 0.6 percentage points of VOQC except in two families. On HHL, it removes 14.4 to 14.8 points more gates. POPQC can beat its own oracle because VOQC runs each of its passes once, in a fixed order. A later pass can create an opportunity that an earlier pass would catch, but VOQC does not run the earlier pass again. By calling VOQC repeatedly on overlapping segments, POPQC can exploit opportunities created by earlier calls.

On Sqrt, POPQC removes 0.9 to 3.4 points fewer gates. More than 5% of Sqrt's gates can move more than 200 positions through commutation, so some gates that could cancel sit more than \\(\Omega = 200\\) gates apart.

# Related work

We introduced local optimality and the oracle in an earlier paper, together with a sequential algorithm, OAC ([Arora et al., 2025](https://arxiv.org/abs/2502.19526)). Like the first approach in [The trouble with boundaries](#the-trouble-with-boundaries), OAC cuts the circuit into blocks, optimizes each with the oracle, and then melds neighboring blocks by re-optimizing across one boundary at a time. It makes a linear number of oracle calls, but it is sequential, and its implementation of cutting and melding adds quadratic overhead. POPQC keeps OAC's guarantee and removes both limitations. Fingers let it revisit changed segments in parallel, while tombstones and the index tree avoid the quadratic overhead. Other circuit optimizers are discussed [above](#why-not-find-the-best-circuit), and newer ones add learning (Quarl, [Li et al., 2024](https://arxiv.org/abs/2307.10120)) or resynthesis (GuoQ, [Xu et al., 2025](https://arxiv.org/abs/2411.04104)). Because POPQC treats the oracle as a black box, any of them could in principle serve as its oracle.

In classical computing, a concept related to local optimality is peephole optimization, which dates back to [McKeeman (1965)](https://doi.org/10.1145/364995.365000) (see also [Cooper and Torczon, 2022](https://shop.elsevier.com/books/engineering-a-compiler/cooper/978-0-12-815412-0); [Bansal and Aiken, 2006](https://doi.org/10.1145/1168857.1168906)). A peephole optimizer rewrites a few instructions at a time, for example three additions into one multiplication, and each such rewrite is cheap. POPQC's segments are much longer, 400 gates for \\(\Omega = 200\\), and each one goes to the oracle, a full optimizer such as VOQC. Each oracle call is therefore expensive, so POPQC must keep the number of calls small.

Local optimality is also related to irreducibility in string rewriting. Define a rewrite rule \\(A \to \mathrm{oracle}(A)\\) for every \\(\Omega\\)-segment \\(A\\) that the oracle can optimize. A circuit is then locally optimal exactly when no rule applies to it. For a finite set of length-reducing rules, a classical algorithm computes an irreducible form of a string in linear time with a left-to-right scan ([Book, 1982](https://doi.org/10.1145/322290.322301); see also Lemma 3.1 of [Diekert, Duncan, and Myasnikov, 2010](https://arxiv.org/abs/0906.2223)). Our \\(O(n)\\) bound on oracle calls rests on a similar potential argument. POPQC carries out this reduction in parallel, with the work and span bounds given above.

Logic synthesis uses similar techniques in a different setting. Like large quantum circuits, its circuits often have millions of gates. There, local optimizations such as rewriting ([Mishchenko, Chatterjee, and Brayton, 2006](https://people.eecs.berkeley.edu/~alanmi/publications/2006/dac06_rwr.pdf)) have been parallelized on multicore CPUs ([Possani et al., 2018](https://doi.org/10.1145/3240765.3240861)) and GPUs ([Liu and Young, 2023](https://doi.org/10.1109/DAC56929.2023.10247961)). POPQC applies a similar approach to quantum circuits.

# Limitations and next steps

- **Gate order.** Local optimality depends on the order in which the gates are listed, although a circuit is better described as a graph of dependencies between gates. Segments defined on that dependency graph could remove the dependence on gate order and expose parallelism across qubits.
- **Other costs.** The potential argument needs a cost that accepted rewrites strictly reduce and that adds up over disjoint segments. *Depth*, the number of time steps, is not such a cost, so extending POPQC to costs like depth is future work.
- **Mapping to hardware.** Real compilers do more than reduce the gate count. They also map a circuit onto the hardware, where only some pairs of qubits can interact, by inserting extra gates that move qubit states around. Whether techniques like ours can also speed up this step is an open question.

---

The [paper](https://arxiv.org/abs/2506.13720) has the details, and the [code](https://github.com/UmutAcarLab/popqc) is on GitHub. POPQC is joint work with Jatin Arora, Mingkuan Xu, and my advisor Umut A. Acar.
