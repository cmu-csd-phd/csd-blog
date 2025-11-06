+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "Computer Assisted Mathematics: A Case Study in Discrete Geometry"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2025-11-06

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Artificial Intelligence", "Theory"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
# Consider these similar to keywords specified for a research paper
tags = ["SAT", "discrete geometry", "Erdős-Szekeres problems", "automated mathematics"]

[extra]
author = {name = "Bernardo Subercaseaux", url = "https://bsubercaseaux.github.io/"}
# The committee specification is a list of objects similar to the author.
committee = [
{name = "William Kuszmaul", url = "https://sites.google.com/site/williamkuszmaul"},
{name = "Jan Hoffmann", url = "https://www.cs.cmu.edu/~janh/"},
{name = "Emre Yolcu", url = "https://www.cs.cmu.edu/~eyolcu/"}
]
+++

# The elephant in the room: AI \& Mathematics

In the last couple of years a pressing question has started to permeate the mathematical community: *_how will mathematicians' jobs coexist harmoniously with AI as it gets progressively better at mathematics?_* ["A.I. Is Coming for Mathematics, Too"](https://www.nytimes.com/2023/07/02/science/ai-mathematics-machine-learning.html) was the title chosen by the NY Times in their dedicated article of 2024, ["AI Will Become Mathematicians' Co-Pilot"](https://www.nytimes.com/2023/07/02/science/ai-mathematics-machine-learning.html) said the Scientific American, and the American Mathematical Society published ["Questions Artificial Intelligence Raises for the Mathematics Profession"](https://www.nytimes.com/2023/07/02/science/ai-mathematics-machine-learning.html).

This time it does not seem to be just a matter of sensationalistic journalism. Some of the most respected mathematicians in the world are joining the conversation, with voices of concern, excitement, and a wide spectrum of positions in between. Perhaps the most aligned with the spirit of this research is Jordan Ellenberg, number theorist who co-authored FunSearch with DeepMind and stated (see [Castekvecchi, 2023](#EllenbergQuote)):

> What’s most exciting to me is modeling new modes of human–machine collaboration,
> I don’t look to use these as a replacement for human mathematicians, but as a force multiplier.

The goal of this post is to show through a concrete case study how SAT solvers, a relatively old AI technology, can also allow for human-machine collaboration in mathematics. 



<!-- The problem we study takes place in two-dimensional geometry, an a priori continuous domain.
 Perhaps surprisingly, we will leverage the capabilities of modern SAT solvers, which reason about boolean formulas, to make progress in  -->
 While this is not the first usage of SAT in discrete geometry, its main novelty (besides the technical results) is in documenting how SAT solvers and other automated reasoning tools can assist mathematical research by revealing patterns and eliciting conjectures. 
 Another advantage of these classic AI tools is _verification_: as opposed to recent language-based forms of AI, standard automated reasoning tools such as (Max)SAT solvers can provide checkable proofs for their answers. This enhances the trustworthiness of the results, which is paramount in computational mathematics.

 This post is based on joint work with John Mackey, Marijn J. H. Heule and Ruben Martins. It was accepted at CICM'2024, where it was the runner-up for best paper award, and it is publicly available at [https://arxiv.org/abs/2311.03645](https://arxiv.org/abs/2311.03645). Naturally, this blog post tells a linearized version of the story; our work went through many back-and-forths, and sometimes intuition preceded computation.

 ## SAT solvers in two paragraphs

 SAT solvers are highly efficient programs for determining whether a boolean formula can be _satisfied_ by some assignment of its variables. For example, the formula
\\(
  (x_1 \lor \neg x_2) \land (x_2 \lor x_3) \land (\neg x_1 \lor \neg x_3)
\\)
is satisfiable, since we can take the assignment \\(x_1 = \top, x_2 = \top, x_3 = \bot \\). Most SAT solvers take boolean formulas in this format, called _conjunctive normal form_ (CNF), in which a formula is a conjunction of _clauses_, where each clause is a disjunction of _literals_ (variables or their negation). 

Even though this _satisfiability_ problem is the archetype of NP-completeness, the engineering advances on both software and hardware allow modern SAT solvers to tackle many instances of interest that arise naturally in mathematics, formal verification, and even cryptography ([Fichte et al., 2023](#silentRevolution)). The MaxSAT variant, in which the goal is to maximize the number of satisfied clauses, is also well-studied and we will also use it later on in this blog.
For a general reference on SAT solvers, I recommend the _Handbook of Satisfiability_ ([Biere et al., 2009](#BiereHandbook)).

# The Happy Ending was just the beginning

In 1933, Esther Klein presented the following problem to George Szekeres and Paul Erdős:

> **Problem 1.** If five points lie on a plane so that no three points form a straight line, prove that four of the points will form a convex quadrilateral.[^quadr]

Klein's solution is simple and elegant; almost entirely explained in **Figure 1**. Note first that there are only three possible cases for the size of the convex hull of five points without collinearities. In case **(a)**, where the convex hull includes all five points, any four of them make a convex quadrilateral. In case **(b)**, where the convex hull has only four points, those four are the sought-after quadrilateral. In case **(c)**, where the convex hull is a triangle, we consider the line \\(L\\) passing through the two points inside the triangle, which we call \\(p_1\\) and \\(p_2\\), and then observe that the pigeonhole principle implies that one side of \\(L\\) must contain two of the three points in the convex hull, which we call \\(p_3\\) and \\(p_4\\); we are done, since the points \\(p_1, p_2, p_3, p_4\\) must form a convex quadrilateral.

<!-- ![Illustration of Klein's proof](./klein_cases.png) -->
<img src="./klein_cases.png" width="500" alt="Illustration of Klein's proof for the existence of a convex quadrilateral among 5 popints in general position." style="display: block; margin: 0 auto">

Klein's problem kickstarted _geometric Ramsey theory_, and it was soon afterwards extended by Szekeres and Erdős into the following theorem:

> **Erdős-Szekeres Theorem.** For any positive integer \\(k\\), there is an integer \\(g\\) such that any set of \\(g\\) points contains either 3 collinear points or a convex \\(k\\)-gon.

For every \\(k\\), the smallest integer \\(g\\) satisfying the theorem is denoted by \\(g(k)\\).

As a second consequence of the problem, George Szekeres and Esther Klein married, which led Erdős to jokingly name Klein's problem the *_Happy Ending problem_*.

Not only has Klein's problem had a long-lasting impact in discrete geometry, but her solution already contains an important insight: properties of finite point sets such as convexity do not rely on the specific coordinates of the points, but rather on their relative position and orientations, which are enough to determine the structure of e.g., convex hulls. This insight, as will become clear later in this post, is what opens the door to discrete computation in a domain which may a priori seem continuous.

# The problem: minimizing convex pentagons

Klein's proof shows that \\(g(4) \leq 5\\), and it is then easy to see that indeed \\(g(4) = 5\\). It is not too hard to see that \\(g(5) = 9\\) (see **Figure 2**), but it took until 2006 for \\(g(6) = 17\\) to be proven computationally by [Lindsay Peters and George Szekeres](#szekeresPeters). [^szekeres] No other values of \\(g(k)\\) are known, although Erdős and Szekeres conjectured \\(g(k) = 2^{k-2} + 1\\) for all \\(k \geq 3\\).

<img src="./g_5_8_9.png" width="500" alt="8 points without convex pentagons" style="display: block; margin: 0 auto">

In 1973, a more quantitative variant was posed by [Erdős and Guy](#erdosGuy):

> More generally, one can ask for the least number of convex \\(k\\)-gons determined by \\(n\\) points in the plane [without three on a line].

Indeed, let us denote by \\(\mu_k(n)\\) the minimum number of convex \\(k\\)-gons on a placement of \\(n\\) points in the plane without any three on a common line. While \\(\mu_4(n)\\) has been heavily studied, its close cousin \\(\mu_5(n)\\) has received significantly less attention, and our goal was to remedy this situation. The following table summarizes our progress in computing \\(\mu_5(n)\\), previously known up to \\(n = 11\\), and now solved up to \\(n = 16\\).

| # of points (\\(n\\)) | ≤8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 |
|-----------------|----|----|----|----|----|----|----|----|----|
| Previously [2]  | 0  | 1  | 2  | 7  | [12, 13] | [20, 34] | [40, 62] | [60, 113] | — |
| Our work        | 0  | 1  | 2  | 7  | 12 | 27 | 42 | 77 | 112 |

# A boolean representation of the problem

As suggested by Klein's proof for \\(g(4)\\), it is possible to reason about geometric properties like convexity based on combinatorial relationships between points instead of their concrete coordinates. Our goal in this section is to see how these relationships between points, and their impact on properties like convexity, can be encoded in propositional logic. The most successful combinatorial abstraction in geometric Ramsey theory is that of _triple orientations_,[^aka] which intuitively consists of considering which ordered triples of points define a curve that turns counterclockwise, and which ones turn clockwise. Concretely, given points \\(p, q, r\\), their _triple orientation_ is defined as

\\[
    \sigma(p, q, r) =  \text{sign} \det \begin{pmatrix} p_x & q_x & r_x \\\ p_y & q_y & r_y \\\ 1 & 1 & 1 \end{pmatrix} = \begin{cases} -1 & \text{if } p, q, r \text{ are oriented clockwise,} \\\\
    0 & \text{if } p, q, r \text{ are collinear}, \\\\
    1 & \text{if } p, q, r \text{ are oriented counterclockwise}.
    \end{cases}
\\]

Since the problem disallows collinear points, we can ignore the case \\(\sigma(p, q, r) = 0 \\), and thus note that each set of points \\((p_1, \ldots, p_n)\\) induces a valuation of propositional variables \\(o_{i, j, k}\\) through \\(o_{i, j, k} \iff \sigma(p_i, p_j, p_k) = 1 \\). We will use these _orientation_ variables, for \\(1 \leq i < j < k \leq n\\), to encode the convex-pentagon minimization condition, assuming without loss of generality that the points are labeled from left to right. The following figure illustrates how convexity is captured by triple orientations, and is invariant to the "details" of the coordinates (i.e., invariant under rotations, reflections, and infinitesimal perturbations)

<img src="./orientations.png" width="500" alt="Illustration of the triple-orientations describing convexity." style="display: block; margin: 0 auto">

 More precisely, to encode whether a given \\(5\\)-tuple of points is convex or not with our orientation variables we can use an idea of [Szekeres and Peters, 2006](#szekeresPeters), who identified a nice separation of the cases leading to convex pentagons just in terms of the triple orientations.

<img src="./szekeres_cases.png" width="600" alt="Cases for a convex pentagon, from Szekres and Peters."  style="display: block; margin: 0 auto">

Every possible convex pentagon falls into exactly one of these cases, and each of these cases can be described succinctly as follows:

* **Case I**:
\\(\sigma(a,b,c) =- \sigma(b,c,d) = -\sigma(c,d,e),\\)
* **Case II**:
  \\( \sigma(a, b, c) =-\sigma(b, c, e) = \sigma(a,d,e),\\)
* **Case III**: \\( \sigma(a,b,d) = -\sigma(b, d, e) = \sigma(a, c, e),\\)
* **Case IV**:  \\( \sigma(a, b, e) = -\sigma(a, c, d) = -\sigma(c, d, e).\\)

We can thus easily encode these cases through the boolean orientation variables. For example, the fact that a tuple \\((a,b,c,d,e)\\) does not fall into the first case can be expressed by the formula

\\[
F^I_{a,b,c,d,e} := (o_{a,b,c} \rightarrow (o_{b,c,d} \vee o_{c,d,e})) \wedge (\neg {o_{a,b,c}} \rightarrow (\neg o_{b,c,d} \vee \neg o_{c,d,e})),
\\]
and similarly, we can construct formulas \\(F^{II}_{a,b,c,d,e}, F^{III}\_{a,b,c,d,e}, F^{IV}\_{a,b,c,d,e} \\) for the remaining cases.

Then, we can write each of these formulas in _conjunctive normal form_ (CNF), recalling that \\( (x \rightarrow y) \equiv (\overline{x} \lor y) \\). The conjunction of all these, over all 5-tuples of points indexed by \\([n]\\), results in a formula \\(\Phi_n\\) such that each convex pentagon on a set of \\(n\\) points in general position would induce exactly one falsified clause in \\(\Phi_n\\). Moreover, some additional symmetry-breaking constraints can be added to the \\(\Phi_n\\) in order to reduce the search space and make the local search more efficient, but we will not discuss them here in order to simplify our exposition. A detailed description, including formally verified proofs of correctness, can be found in [Subercaseaux et al., 2024](#Verification).

<!-- \\[
F^{I}_{a,b,c,d,e} := (o_{a,b,c} \rightarrow (o_{b,c,d} \vee o_{c,d,e}) ) \wedge (\overline{o_{a,b,c}} \rightarrow (\overline{o_{b,c,d}} \vee \overline{o_{c,d,e}}))
\\] -->
<!-- 
Now, to minimize the number of convex pentagons instead of fully forbidding them, we can introduce a relaxation variable \\(r_{a,b,c,d,e}\\) for each 5-tuple of points, and then replace each clause \\(C_{a,b,c,d,e}\\) forbidding a convex pentagon by

\\(
C_{a,b,c,d,e} \lor r_{a,b,c,d,e}
\\) -->

# Local search

At this point, we can use a local search SAT solver (e.g., _Tassat_ ([Chowdhury, Codel, Heule, 2023](#Tassat))) to try to minimize the number of falsified clauses in the formula \\(\Phi_n\\), and thus, indirectly, the number of convex pentagons among \\(n\\) points. We need however to declare two caveats:
- Local search solvers can get stuck at local minima, so the number of falsified clauses they obtain is only an upper bound on the true answer.
- Unfortunately, the upper bound on the number of falsified clauses does not provide an upper bound on the minimum number of convex pentagons, since assignments to the orientation variables might not be _realizable_ by any set of actual points in the plane. In fact, the _realizability problem_ of deciding whether an assignment to the orientation variables matches the orientations of some set of points in the plane is \\(\exists \mathbb{R} \\)-complete, so much harder than SAT itself.

Despite these worst-case warnings, by running local search we obtained the following results:

<div style="display: flex; gap: 20px;">
<div style="flex: 50%;">

|  \\(n\\) | Min. false cls | time [s] |  
|----|----|----|
| 9  | 1  | 0.00  | 
| 10 | 2  | 0.00  | 
| 11 | 7  | 0.00  | 
| 12 | 12  | 0.00  | 
| 13 | 27 | 0.01  | 
| 14 | 42  | 0.01  | 
| 15 | 77  | 0.01  | 
| 16 | 112 | 0.02  | 
| 17 | 182| 0.02  | 
| 18 | 252  | 2.03  | 
| 19 | 378  | 0.94  | 
</div>
<div style="flex: 50%;">

|  \\(n\\) | Min. false cls | time [s] | 
|----|----|----|
| 20 | 504  | 174.11  | 
| 21 | 714  | 3.34  | 
| 22 | 924  | 43.92  | 
| 23 | 1254  | 11.64  | 
| 24 | 1584  | 472.33  | 
| 25 | 2079  | 63.48  | 
| 26 | 2574  | 5268.1  | 
| 27 | 3289  | 1555.5  | 
| 28 | 4004  | 1791.9  | 
| 29 | 5005  | 467.36  | 
| 30 | 6007  | 18244  |
</div>
</div>

Can you notice any patterns?
For a first observation, let's see the sequence of differences between consecutive values:
\\( 1, 5, 5, 15, 15, 25, 25, 70, 70,
126, 126, ...\\) These is hardly a coincidence, as we will show later. But more importantly, can we see a function that describes this sequence? *Wolfram Mathematica* certainly can! If we interpolate the first ten even values by a degree 5-polynomial (a natural guess since these are a fraction of the 5-tuples of points), the answer is immediate: \\( 2\binom{N/2}{5}\\). This formula matches all the even terms except the last one, which is off by one. Considering the runtime and the fact that it's also the first time the consecutive differences differ (\\(6007 - 5005 \neq 5005 -4004\\)), the simplest interpretation is that local search caps out around \\(n = 30\\), but the answer most likely is indeed \\(6006\\).  
Playing with the odd values quickly suggests the following conjecture for all values of \\(n\\):

\\[
  \mu_5(n) = \binom{\lfloor{n/2}\rfloor}{5} + \binom{\lceil{n/2}\rceil}{5}.
\\]

Note that this conjecture directly implies the observation about consecutive differences:
\\[
  \mu_5(2n) - \mu_5(2n-1) = 2\binom{n}{5} - \left(\binom{n}{5} + \binom{n-1}{5}\right) = \binom{n}{5} - \binom{n-1}{5} = \binom{n-1}{4}
\\]
and similarly
\\[
  \mu_5(2n-1) - \mu_5(2n-2) = \left(\binom{n}{5} + \binom{n-1}{5}\right) - 2\binom{n-1}{5} = \binom{n}{5} - \binom{n-1}{5} = \binom{n-1}{4}.
\\]


# Constructions

As we mentioned, however, we have no a-priori guarantee that the local search solutions are actually realizable by points in the plane. In fact, the fraction of orientation assignments that can be realized goes to zero as \\(n\\) grows, at a rate of \\(2^{-n}\\) ([Knuth, 1992](#knuthAxiomsHulls)). 

Once again, not discouraged by the worse-case analysis, implementing a realizability program yields insightful results. [^realizer]  Indeed, by realizing different assignments for \\( n = 12\\), we obtained two classes of realizations:

<img src="./realizations.png" width="600" alt="Realizations for local-search assignments over 12 points."  style="display: block; margin: 0 auto">


Naturally, we gave John Mackey, the mathematician in the group, the task of proposing general constructions of these shapes.
We called the left one a _pinwheel construction_, and the right one a _parabolic construction_.

<img src="./constructions.png" width="600" alt="Illustrations of the upper bound constructions"  style="display: block; margin: 0 auto">


Interestingly, they both give the conjectured answer in general, thus making it a proper upper bound.

> **Theorem 1**: For every \\(n \geq 9\\), we have \\(\mu_5(n) \leq \binom{\lfloor{n/2}\rfloor}{5} + \binom{\lceil{n/2}\rceil}{5}\\).

 Seeing this in the pinwheel construction requires a bit of work, but in the parabolic construction it is rather easy to see. It suffices to show, as **Figure 7** (below) illustrates, that the subsets of 5 points that are convex are precisely those that are contained in a single parabola.

<img src="./parabollic.png" width="600" alt="Detail of the parabolic construction."  style="display: block; margin: 0 auto">

Naturally, even the parabolic construction requires some care in the design of the parabolas. A concrete construction that works is to define the parabolas \\(L^{\top}\\) and \\(L^{\bot}\\) based on the points
\\[
    p^\top_i = \left(i, 2  + \frac{i^2}{n^2}\right), \forall i \in  \left[\left\lfloor\frac{n}{2}\right\rfloor \right] \quad \text{and} \quad
    p^\bot_i = \left(i, -2  - \frac{i^2}{n^2}\right), \forall i \in \left[\left\lceil\frac{n}{2}\right\rceil \right].
\\]



# Verification

Since local search solvers cannot prove lower bounds, we used a MaxSAT formulation to certify the values \\(\mu_5(n)\\) for \\(n \leq 15\\). Concretely, the solver that performed best was _MaxCDCL_ ([Li et al., 2021](#MaxCDCL)), and we used a _Cube and Conquer_ ([Heule, Kullman, Biere, 2018](#CubeAndConquer)) approach to parallelize the computation. Then, the _VeritasPBLib_ ([Gocht et al., 2022](#Veritas)) framework allowed us to obtain a reproducible certificate. Such certificates prove facts of the form "at most \\(k\\) clauses can be satisfied in formula \\(F\\)" by showing

1. A new formula \\(F'\\), constructed based on \\(F\\) and \\(k\\), such that \\(F'\\) is satisfiable if and only if some assignment can satisfy \\(k+1\\) or more clauses in \\(F\\).
This relation between \\(F'\\) and \\((F, k)\\) is formally proven through the _cutting planes_ method. 
2. That \\(F'\\) is unsatisfiable, which is formally certified using the (by now standard) DRAT proof format, for which formally verified proof-checkers exist.

A reasonable analogy for how a "proof of unsatisfiability" looks like is as follows: consider a set of linear equations for which we want to show there is no solution. Then, a proof could list a sequence of operations, as for example
1. multiply both sides of equation (7) by \\(-3\\),
2. add equations (2) and (5) together, resulting in a new equation (9), 
3. subtract \\(2x\\) from both sides of equation (4).

Given a finite set of such valid operations, we may decide on a standardized format to list them, as for instance
```
mul eq7 -3: eq7
add eq2 eq5: eq9
add eq4 -2x: eq10
```
Then, we may also decide on a canonical example of impossibility: \\( 0 = 1\\), meaning that if we can derive this equation from our original set, then the original set has no solution, and all proofs must end by deriving exactly this equation. 

The case of unsatisfiability proofs is analogous: proofs list a sequence of basic operations \\(F_i \to_{\text{op}} F_{i+1}\\) that iteratively transform a CNF formula while preserving satisfiability. The proof ends when \\(F_{n}\\) contains an empty clause, which is the canonical "\\(0 = 1\\)" example of unsatisfiability.


The details are purposefully omitted here (and the interested reader can find them in [Heule, 2016](#DRAT)), but the important part is that SAT and MaxSAT solvers can emit checkable proofs of their results, and moreover, some of the proof-checkers have been formally verified in theorem provers such as HOL4 ([Tan, Heule, and Myreen, 2021](#CakeLPR), [Boaerts et al., 2023](#CakePB)).
This is particularly important for applications to mathematics, where correctness is paramount, and there is experience of computer-assisted proofs containing mistakes (cf. the original proof of the four color theorem, now formally verified by [Gonthier, 2023](#fourColor)). Hence, it is also important to mention that an important concern with computer-proofs is the correspondence between the computation and the mathematical statement it intends to prove. For example, even if a formula \\(F\\) is formally proven to be unsatisfiable, it could be the case that \\(F\\) is not a correct encoding of the mathematical statement we have in mind, making its unsatisfiability irrelevant. Because of the subtleties that naturally appear in translating geometric properties to propositional logic, this is a particularly important concern in our case. To this end, together with a group of students at CMU, we formally verified in Lean that the logical constraints and symmetry-breaking predicates we used in this work, and other similar proofs about discrete geometry, are indeed correct ([Subercaseaux et al., 2024](#Verification)).


# Let's make it 16.

We can actually leverage the insight of the consecutive differences from earlier on to certify the value of \\(\mu_5(16)\\) without having to run a MaxSAT solver.

 First, consider the following _supersaturation_ lemma.

> **Lemma 2**: For every \\(n > 5\\), we have \\(\mu_5(n) \geq \frac{n}{n-5} \cdot \mu_5(n-1)\\).

_Proof_. Consider a set of \\(n\\) points \\(S\\) that achieves the optimal bound, and for each point \\(p \in S\\) let \\(f(p)\\) be the number of convex pentagons in \\(S\\) that contain \\(p\\). As pentagons consist of exactly five points, we have \\(\sum_{p \in S} f(p) = 5 \cdot \mu_5(n)\\). Now, notice that for every \\(p\\) there must be at least \\(\mu_5(n-1)\\) convex pentagons that do not contain \\(p\\), and thus we have \\( \mu_5(n) - f(p) \geq \mu_5(n-1)\\). Summing this equation over \\(p\\) gives us
\\[
\sum_{p \in S} (\mu_5(n) - f(p)) \geq n \cdot \mu_5(n-1),
\\]
and as \\(\sum_{p \in S} (\mu_5(n) - f(p)) = n \cdot \mu_5(n) - 5 \cdot \mu_5(n)\\), we have the desired inequality.


Now, combining this with **Theorem 1**, we can formalize our previous observation:

> **Theorem 2**: If for some \\(n > 5\\) it holds that \\(\mu_5(2n-1) = \binom{n}{5} + \binom{n-1}{5}\\), then we have \\(\mu_5(2n) = 2\binom{n}{5}\\).

_Proof_. We have \\(\mu_5(2n) \leq 2\binom{n}{5}\\) by **Theorem 1**, and thus to see that equality is achieved we use **Lemma 2** to obtain
\\[
  \mu_5(2n) \geq \frac{2n}{2n-5} \mu_5(2n-1) = \frac{2n}{2n-5} \left(\binom{n}{5} + \binom{n-1}{5}\right),
\\]
and since \\(\binom{n}{5} = \frac{n}{n-5} \binom{n-1}{5}\\), we have
\\[
  \frac{2n}{2n-5} \left(\binom{n}{5} + \frac{n-5}{n} \binom{n}{5}\right) = \left(\frac{2n}{2n-5} + \frac{2(n-5)}{2n-5}\right)\binom{n}{5} = 2\binom{n}{5}.
\\]

Thus, from the fact \\(\mu_5(15) = 77\\), we conclude that \\(\mu_5(16) = 112\\).
<!-- What can we say about $\mu_5(n)$? Well, from $g(5) = 9$ we at least get that $\mu_5(n) = 0$ for $n < 9$, and $\mu_5(9) \geq 1$. We can leverage this fact as follows. If we have for instance $90$ points in the plane, and partition them into $10$ groups of $9$ points, we know that each group must contain at least one convex pentagon, and thus $\mu_5(90) \geq 10$. This folklore "supersaturation" idea can be extended further:

> **Lemma 1**: Let $m$ and $r$ be values such that $\mu_k(m) \geq r$. Then, for every $n \geq m$ we have

$$

\mu_k(n) \geq r \cdot \binom{n}{m}/\binom{n-k}{m-k} = r \binom{n}{k}/\binom{m}{k}.

$$

_Proof_.  -->

<!-- The value of $g(7)$ is conjectured to be $33$, and more in general, Erdős and Szekeres conjectured $g(k) = 2^{k-2} + 1$. In 1961, Erdős and Szekeres proved $g(k) \geq 2^{k-2} + 1$, and to this day, the best upper bound is $g(k) \leq 2^{k + O(\sqrt{k \log k})}$ -->

# Conclusions

We have seen, through a concrete case study, how SAT solvers, coupled with other computational tools, can assist mathematical research at different stages. At the moment, the mathematical community is trying to understand how to best leverage AI for mathematics, and it is important to document how existing tools can also be used in this context. While the current conversation is centered around language models, I strongly believe that classical AI tools are still vastly underutilized by the mathematical community, and I plan to keep working on tools, algorithms, and logical encodings that might make them more popular among mathematicians.



---
## Bibliography

- <a name="BiereHandbook"></a> Biere, A., Heule, M. J. H., van Maaren, H., and Walsh, T. (eds.) (2009). Handbook of Satisfiability. IOS Press. <https://www.iospress.com/catalog/books/handbook-of-satisfiability-2/>

- <a name="silentRevolution"></a> Fichte, J. K., Le Berre, D., Hecher, M., and Szeider, S. (2023). The Silent (R)evolution of SAT. Communications of the ACM, 66(6), 64–72. <https://doi.org/10.1145/3560469>

- <a name="szekeresPeters"></a> Szekeres, G., and Peters, L. (2006). Computer solution to the 17-point Erdős–Szekeres problem. ANZIAM Journal, 48(2), 151–164. <https://doi.org/10.1017/S144618110000300X>

- <a name="signotopes"></a> Felsner, S., and Weil, H. (2001). Sweeps, arrangements and signotopes. Discrete Applied Mathematics, 109(1), 67–94. <https://doi.org/10.1016/S0166-218X(00)00232-8>

- <a name="DRAT"></a> Heule, M. J. H. (2016). The DRAT format and DRAT-trim checker. <https://arxiv.org/abs/1610.06229>

- <a name="knuthAxiomsHulls"></a> Knuth, D. E. (1992). Axioms and Hulls. Lecture Notes in Computer Science, 606. Springer, Berlin/Heidelberg. <https://doi.org/10.1007/3-540-55611-7>

- <a name="Tassat"></a> Chowdhury, M. S., Codel, C. R., and Heule, M. J. H. (2024). TaSSAT: Transfer and Share SAT. In: Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2024), ETAPS 2024, Luxembourg City, Luxembourg, April 6–11, 2024. Proceedings, Part I (pp. 34–42). Springer, Berlin/Heidelberg. <https://doi.org/10.1007/978-3-031-57246-3_3>

- <a name="MaxCDCL"></a> Li, C., Xu, Z., Coll, J., Manyà, F., Habet, D., and He, K. (2021). Combining clause learning and branch and bound for MaxSAT. In: 27th International Conference on Principles and Practice of Constraint Programming (CP 2021). Leibniz International Proceedings in Informatics (LIPIcs), 210, 38:1–38:18. Schloss Dagstuhl—Leibniz-Zentrum für Informatik. <https://doi.org/10.4230/LIPIcs.CP.2021.38>

- <a name="Veritas"></a> Gocht, S., Martins, R., Nordström, J., and Oertel, A. (2022). Certified CNF translations for pseudo-Boolean solving. In: 25th International Conference on Theory and Applications of Satisfiability Testing (SAT 2022). Leibniz International Proceedings in Informatics (LIPIcs), 236, 16:1–16:25. Schloss Dagstuhl—Leibniz-Zentrum für Informatik. <https://doi.org/10.4230/LIPIcs.SAT.2022.16>

- <a name="Verification"></a> Subercaseaux, B., Nawrocki, W., Gallicchio, J., Codel, C., Carneiro, M., and Heule, M. J. H. (2024). Formal verification of the empty hexagon number. In: 15th International Conference on Interactive Theorem Proving (ITP 2024). Leibniz International Proceedings in Informatics (LIPIcs), 309, 35:1–35:19. Schloss Dagstuhl—Leibniz-Zentrum für Informatik. <https://doi.org/10.4230/LIPIcs.ITP.2024.35>

- <a name="EllenbergQuote"></a> Castelvecchi, D. (2023). DeepMind AI outdoes human mathematicians on an unsolved problem. Nature, 625(7993), 12–13. <https://doi.org/10.1038/d41586-023-04043-w>

- <a name="CubeAndConquer"></a> Heule, M. J. H., Kullmann, O., and Biere, A. (2018). Cube-and-conquer for satisfiability. In: Hamadi, Y., and Sais, L. (eds.), Handbook of Parallel Constraint Reasoning (pp. 31–59). Springer, Cham. <https://doi.org/10.1007/978-3-319-63516-3_2>

- <a name="CakeLPR"></a> Tan, Y. K., Heule, M. J. H., and Myreen, M. O. (2021). cake_lpr: Verified propagation redundancy checking in CakeML. In: Groote, J. F., and Larsen, K. G. (eds.), Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2021). Lecture Notes in Computer Science, 12652, 223–241. Springer, Cham. <https://doi.org/10.1007/978-3-030-72013-1_12>

- <a name="CakePB"></a> Bogaerts, B., McCreesh, C., Myreen, M. O., Nordström, J., Oertel, A., and Tan, Y. K. (2023). VeriPB and CakePB in the SAT Competition 2023. Report. <https://satcompetition.github.io/2024/downloads/checkers/veripb.pdf>

- <a name="erdosGuy"></a> Erdős, P., and Guy, R. K. (1973). Crossing number problems. American Mathematical Monthly, 80(1), 52–58. <https://doi.org/10.1080/00029890.1973.11993230>

- <a name="fourColor"></a> Gonthier, G. (2023). A computer-checked proof of the Four Color Theorem. Inria report. <https://inria.hal.science/hal-04034866>


---

## Footnotes

[^quadr]: The standard definition of convexity for subsets of \\(\mathbb{R}^2\\) is that a set \\(S\\) is convex if for every two points \\(p, q \in S\\), the line segment joining \\(p\\) and \\(q\\) is also contained in \\(S\\). That is, for any \\(\alpha \in [0, 1]\\) the point \\( \alpha p + (1-\alpha) q\\) belongs to \\(S\\).
 The convex hull of a set of points \\(P\\), denoted \\(h(P)\\), is the smallest convex set containing \\(P\\), that is, the intersection of all convex sets containing \\(P\\).
A set of points \\(S\\) is said to be in _convex position_ if all its points are vertices of its convex hull, i.e., \\( h(S) \neq h(S \setminus \{p\}) \\) for every \\(p \in S\\). A set of \\(k\\) points in convex position is called a _convex k-gon_. For \\(k = 3\\), we also call them triangles, for \\(k = 4\\), convex quadrilaterals, and for \\(k = 5\\), convex pentagons.





[^szekeres]: George Szekeres died in 2005 (one hour apart from Esther Klein!), and thus to the best of my knowledge, Peters completed the paper using some previous ideas of Szekeres, which makes unclear whether the Hungarian mathematician got to see the result \\(g(6) = 17\\) before his passing.


[^aka]: Also known as _signotopes_ [2], Knuth's counterclockwise relation (CC-systems) [3], or _signatures_ [1].

[^realizer]: I have developed since a much more efficient version of this program, leveraging parallelism and a much better algorithm. It can be found in [https://github.com/bsubercaseaux/point_realizer](https://github.com/bsubercaseaux/point_realizer).