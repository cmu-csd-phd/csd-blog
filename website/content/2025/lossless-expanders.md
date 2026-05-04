+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "Explicit Lossless Vertex Expanders"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2025-06-30

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Theory"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
# Consider these similar to keywords specified for a research paper.
tags = ["vertex-expanders", "explicit-constructions", "Ramanujan-graphs"]

[extra]
author = {name = "Jun-Ting Hsieh", url = "https://jthsieh.github.io/" }
# The committee specification is  a list of objects similar to the author.
committee = [
    {name = "Aayush Jain", url = "https://sites.google.com/view/aayushjain/home"},
    {name = "David P. Woodruff", url = "https://www.cs.cmu.edu/~dwoodruf/"},
    {name = "Noah Singer", url = "https://noahsinger.org/"}
]
+++


In this blog post, I will explain a series of 3 papers, where the third one gives the first construction of explicit constant-degree lossless vertex expanders.

* [[HMMP24](#HMMP24)] [Explicit two-sided unique-neighbor expanders](https://arxiv.org/abs/2302.01212). With Theo McKenzie, Sidhanth Mohanty, Pedro Paredes.
STOC, 2024.

* [[HLMOZ25](#HLMOZ25)] [Explicit Two-Sided Vertex Expanders Beyond the Spectral Barrier](https://arxiv.org/abs/2411.11627).
With Ting-Chun Lin, Sidhanth Mohanty, Ryan O'Donnell, Rachel Yun Zhang.
STOC, 2025.

* [[HLMRZ25](#HLMRZ25)] [Explicit Lossless Vertex Expanders](https://arxiv.org/abs/2504.15087).
With Alexander Lubotzky, Sidhanth Mohanty, Assaf Reiner, Rachel Yun Zhang.
Preprint, 2025.


The third paper should be easy to understand, and its introduction contains a fairly thorough discussion and technical overview.
In this blog post, I will talk about the journey, provide more intuition, and explain some heuristic calculations we did when working on the problem.
I will focus on the key ingredient --- the **tripartite line product** --- which is the main object underlying all 3 papers.


# Introduction

We start with the definition of vertex expanders.

> **Definition** (Vertex expander).
> We say that a \\(d\\)-regular graph \\(G = (V, E)\\) is a \\(\gamma\\)-vertex expander if there is a constant \\(\eta\\) (depending only on \\(d\\)) such that every subset \\(S \subseteq V\\) of size at most \\(\eta |V|\\) has at least \\(\gamma d |S|\\) distinct neighbors.

Here, we focus on infinite families of constant-degree graphs \\((G_n)_n\\), where the size of the graphs grow to infinity while the parameters \\(d, \gamma, \eta\\) stay constant.
Ideally, if we can make \\(\gamma\\) to be \\(1-\varepsilon\\) for an arbitrarily small \\(\varepsilon\\), then we call these **lossless expanders**.

Lossless expansion is essentially the strongest form of expansion.
Any subset \\(S \subseteq V\\) has \\(d|S|\\) incident edges, so \\((1-\varepsilon)\\)-expansion means that almost all incident edges go to distinct vertices outside of \\(S\\).
It is easy to see, by Markov's inequality, that \\(S\\) must have at least \\((1-2\varepsilon) d|S|\\) *unique-neighbors* --- vertices with exactly one edge connected to \\(S\\).
Unique-neighbor expansion is a very important property in many applications, though we will not make the distinction in this post.

We also consider *bipartite vertex expanders*.
The definition is straightforward.


> **Definition** (Two-sided vertex expander).
> We say that a \\((d_L, d_R)\\)-biregular graph \\(G = (L, R, E)\\) is a two-sided \\(\gamma\\)-vertex expander if there is a constant \\(\eta\\) (depending only on \\(d_L,d_R\\)) such that
> * every subset \\(S \subseteq L\\) of size at most \\(\eta |L|\\) has at least \\(\gamma d |S|\\) distinct neighbors on the right,
> * every subset \\(T \subseteq R\\) of size at most \\(\eta |R|\\) has at least \\(\gamma d |T|\\) distinct neighbors on the left.

For many applications, it is crucial to construct bipartite graphs with arbitrary *imbalance* \\(d_L / d_R = |R| / |L|\\).
For example, for applications in constructing error-correcting codes, the imbalance determines the *rate* of the code.

**Random graphs:** Random \\(d\\)-regular graphs are lossless expanders with high probability.
However, the problem is that given such a graph, we do not know how to verify (in polynomial-time) that it indeed has good vertex expansion (with hardness evidence given by [[KY24](#KY24)]).
For many applications, we need to be certain that the graphs satisfy the desired properties.
This is why we want *explicit constructions*, which basically mean that
there is a deterministic algorithm that generates these graphs in time polynomial in the size of the graph.


In this blog post, I will skip discussions about prior works on spectral expanders (i.e., Ramanujan graphs) and 1-sided lossless expanders (where only small subsets on the left have vertex expansion).
For more discussion of the history, see the introduction of [[HLMRZ25](#HLMRZ25)].


<!--

## Quest for explicit constructions


What about Ramanujan graphs?
These are optimal spectral (or edge) expanders where the second eigenvalue of the adjacency matrix is at most \\(2\sqrt{d-1}\\).
There are famous explicit constructions of Ramanujan graphs by
[Lubotzky, Phillips \& Sarnak, 1988](https://link.springer.com/article/10.1007/BF02126799),
[Margulis, 1988](https://mathscinet.ams.org/mathscinet/article?mr=939574),
and [Morgenstern, 1994](https://www.sciencedirect.com/science/article/pii/S0095895684710549).
These graphs are optimal spectral expanders, but are they lossless vertex expanders?

Well, we don't know.
We do know that spectral expansion implies \\(\frac{1}{2}\\)-vertex expansion due to [Kahale, 1995].
Unfortunately, in the same paper, Kahale proved that \\(\frac{1}{2}\\) is an inherent barrier if we only assume spectral expansion:
there are near-Ramanujan graphs that contain small subsets \\(S\\) with exactly \\(0.5 d|S|\\) neighbors, and more strikingly, *zero* unique-neighbors.

Thus, even going beyond \\(\frac{1}{2}\\) vertex expansion --- which we call the **spectral barrier** --- is considered a major open question.
For more discussions, see the survey of [Hoory, Linial \& Wigderson, 2006], and also 
a [recent talk](https://www.youtube.com/watch?v=5eGoy6NfkZE) by Irit Dinur
and [this Simons newsletter](https://simons.berkeley.edu/news/theory-institute-beyond-february-2025) by Nikhil Srivastava.


**One-sided vertex expanders:**
For biregular graphs, there is a weaker notion called one-sided expansion, where only small subsets on the left have vertex expansion.
One-sided lossless expanders are known since the seminal work of [Capalbo, Reingold, Vadhan \& Wigderson, 2002] using the zig-zag product.
Recently, [Golowich, 2024] and independently [Cohen, Roth \& Ta-Shma, 2023] gave simpler constructions, based on the work of [Asherov \& Dinur, 2023].

These works all build on the *line product* introduced by [Alon \& Capalbo, 2002], and they provide crucial insights to our works.
We will see later that all these recent constructions can be captured in our generalized *tripartite line product* framework.

We also mention the work of [Chattopadhyay, Gurumukhani, Ringach \& Zhao, 2024].
They studied the bipartite graphs of [Kalev \& Ta-Shma, 2022], which have *polynomially large* imbalance, and showed that they have two-sided lossless expansion ---  the first construction of two-sided lossless expanders in the unbalanced setting.
The non-sparse and unbalanced setting seems to require significantly different ideas than our setting of constant degrees and constant imbalance.

For more history and related works, see the introduction of [Hsieh, Lubotzky, Mohanty, Reiner \& Zhang, 2025].

-->


## Our results

In [[HMMP24](#HMMP24)], we construct the first two-sided \\(\gamma\\)-unique-neighbor expanders, where \\(\gamma\\) is a tiny universal constant.
Later, in [[HLMOZ25](#HLMOZ25)], we construct two-sided \\(0.6\\)-vertex expanders, breaking the "spectral barrier" of \\(0.5\\).
Finally, in [[HLMRZ25](#HLMRZ25)], we achieve the final goal of two-sided lossless expanders.
Here's the formal statement:

> **Theorem 1** (Two-sided lossless expanders).
> For every \\(\varepsilon\\) and imbalance \\(\beta \in (0,1]\\), there exist \\(k, d_0 \in \mathbb{N}\\) such that for any \\(d_L, d_R \geq d_0\\) for which \\(\beta \leq d_L / d_R \leq \beta + \varepsilon\\), there is an explicit infinite family of \\((kd_L, kd_R)\\)-biregular graphs that are two-sided \\((1-\varepsilon)\\)-vertex expanders.

We make a few remarks.
In the case of \\(d_L = d_R = d\\), we can actually get constructions for all \\(d \geq d_0\\) (as opposed to only multiples of \\(k\\)) by simply removing perfect matchings.
Our construction also admits a *free group action* by a group of size linear in the number of vertices (which we will not discuss in this post).
As a consequence, by the work of [[LH22](#LH22)], our construction yields a new family of good quantum LDPC codes that admit linear-time decoding algorithms (see [[LH22](#LH22)] and our paper for more details).

In all 3 papers, the construction uses the **tripartite line product** between a suitably chosen base graph and a constant-sized "random" gadget graph.


# Tripartite line product

The tripartite line product has two ingredients:

1. **Base graph** \\(G\\): a large tripartite graph on vertex sets \\(L, M, R\\) (left, middle, and right), where we place a \\((k, D_L)\\)-biregular graph \\(G_L\\) between \\(L\\) and \\(M\\), and a \\((D_R, k)\\)-biregular graph \\(G_R\\) between \\(M\\) and \\(R\\).

2. **Gadget graph** \\(H\\): a small \\((d_L, d_R)\\)-biregular graph on vertex sets \\([D_L]\\) and \\([D_R]\\).


> **Definition** (Tripartite line product).
> The tripartite line product between \\(G\\) and \\(H\\), denoted \\(G \diamond H\\), is the \\((k d_L, kd_R)\\)-biregular graph on \\(L\\) and \\(R\\) obtained as follows:
> for each vertex \\(v\in M\\), we "place" a copy of \\(H\\) on \\(v\\) --- we connect the \\(D_L\\) left neighbors of \\(v\\) and \\(D_R\\) right neighbors of \\(v\\) such that it forms a local copy of \\(H\\).

This is best explained by a figure:

<a name="tripartite"></a>
![The tripartite line product between a base graph G and gadget graph H.](./tripartite-product.png)

*Figure 1. The tripartite line product between a base graph \\(G\\) and gadget graph \\(H\\). In this figure, we only show the edges from the copy of \\(H\\) coming from a single vertex, in this case the red vertex.*


It is easy to see that the final product is \\((k d_L, k d_R)\\)-biregular:
every vertex in \\(L\\) has \\(k\\) neighbors in \\(M\\), each of them gets a copy of \\(H\\) which has left-degree \\(d_L\\), so the total left-degree is \\(kd_L\\).
The right-degree follows similarly.

There is an important detail that we omit in the definition.
We will assume that the base graph \\(G\\) has an implicit labeling of the edges (like in [Figure 1](#tripartite)), so that when we place the gadget on each middle vertex, we know how to connect the left and right neighbors.
It is very crucial in our second and third papers that we place the gadgets systematically, as we need a certain "spreadness" property from the gadget (this will be explained [later](#middle-to-right-hdx)).

**Parameters:** 
For the purpose of this blog post, let's assume \\(D_L = D_R = D\\) and \\(d_L = d_R = d\\) (thus also \\(|L| = |R|\\)) for simplicity.
It's good to keep the following in mind:

* \\(|L|, |M|, |R|\\) are growing to infinity.

* \\(k\\) is a small constant.
\\(k\\) is any fixed constant in our first paper, \\(k=5\\) in our second paper,
and \\(k = k(\varepsilon)\\) depending only on \\(\varepsilon\\) (for \\((1-\varepsilon)\\)-vertex expanders) in our third paper.

* \\(D\\) is a very large constant (think \\(2^{100k^2}\\)). It is still a constant compared to the number of vertices, but it is convenient to think of it as growing too.

* \\(d\\) will be roughly \\(\sqrt{D}\\) or \\(D^{1/4}\\), but we will set this later.


## Gadget graph

The gadget graph \\(H\\) is of constant size (since \\(D\\) is a constant).
Therefore, we can brute-force search over all \\((d, d)\\)-biregular graphs in constant time.
We always think of the gadget as a *random* \\((d, d)\\)-biregular graph, since random graphs basically satisfy everything we want with high probability.
Of course, we need to do some work to prove these properties (like in the Appendix of [[HMMP24](#HMMP24)]), but this is not the interesting part.


## Base graph

The choice of the base graph (i.e., the two bipartite graphs \\(G_L, G_R\\)) is crucial.

1. In [[HMMP24](#HMMP24)], we use explicit near-Ramanujan bipartite graphs.
There are many existing ones, for example [[MOP20](#MOP20)].

2. In [[HLMOZ25](#HLMOZ25)], we use the face-vertex incidence graphs of high-dimensional expanders (HDX), specifically the 4D Ramanujan complexes by Lubotzky, Samuels and Vishne [[LSV05](#LSV05)].

3. In [[HLMRZ25](#HLMRZ25)], we use the face-vertex incidence graphs of expanding cubical
complexes based on LPS Ramanujan graphs [[LPS88](#LPS88)], constructed (in a different form) by [[RSV19](#RSV19)].


## Local to global

At a high level, the tripartite line product falls in the general framework of "lifting" a local, constant-sized object to large (or infinite families of) objects that inherit the good properties of the local object.
Famous examples include the zig-zag product that lifts a local expander, Tanner codes that lift a local code, and recently high-dimensional expanders, and many more.
Check out Irit Dinur's [recent talk](https://www.youtube.com/watch?v=5eGoy6NfkZE) on the local to global phenomenon.


## Why is it called a "line" product?

The tripartite line product is a generalization of the line product introduced by Alon and Capalbo [[AC02](#AC02)].
Given a \\(D\\)-regular graph \\(G\\) and a gadget graph \\(H\\) on \\(D\\) vertices, the line product between \\(G\\) and \\(H\\) is the graph with vertex set \\(E(G)\\) and edges obtained by placing a copy of \\(H\\) on the \\(D\\) incident edges of each vertex in \\(G\\).
This can be viewed as a special case of \\(k=2\\) in the tripartite line product, where we use the vertex-edge incidence graph of \\(G\\) as the bipartite base graphs (technically, this forms a bipartite version of the line product, but they are basically the same).
Note that if \\(H\\) is a \\(D\\)-clique, then this product is exactly the [line graph](https://en.wikipedia.org/wiki/Line_graph) of \\(G\\) (where two edges are connected if they share a vertex), hence the name.


# Analysis of the tripartite line product

The nice thing about the tripartite line product is that it is symmetric.
Once we prove that subsets on the left expand, then the proof for subsets on the right is almost identical (unless the left and right parameters are very different).

**Notations:**
For simplicity, we assume that \\(D = D_L = D_R\\) and \\(d = d_L = d_R\\).
Recall that the base graphs consist of bipartite graphs \\(G_L = (L, M, E_L)\\) and \\(G_R = (M, R, E_R)\\), which are 
\\((k,D)\\)- and \\((D,k)\\)-biregular respectively.
The gadget graph \\(H\\) is \\((d,d)\\)-biregular on vertex set \\([D] \times [D]\\).
The final product is denoted \\(Z = G \diamond H\\) and has degree \\(kd\\).
We use \\(N_L(v)\\) to denote the set of neighbors of a vertex \\(v\\) in \\(G_L\\), and similarly we use \\(N_R(v)\\) to denote the neighbors of \\(v\\) in \\(G_R\\).


Consider a subset \\(S \subseteq L\\).
Our end goal is to prove that \\(|N_Z(S)| \geq \gamma kd|S|\\) for \\(\gamma\\) as close to \\(1\\) as possible.
Let \\(U = N_L(S) \subseteq M\\) be the neighbors of \\(S\\) in the base graph \\(G_L\\).
For each \\(u\in U\\), its left-neighbors \\(N_L(u)\\) will be connected to vertices in \\(R\\) according to the gadget \\(H\\) (that is, the copy placed on \\(u\\)).

> *Red edges.* For each \\(u\in U\\) and the vertices in \\(R\\) that are connected in \\(Z\\) to \\(N_L(u) \cap S\\) via the local gadget, we color the edges between them *red*.
> The red edges form a subgraph of \\(G_R\\).

> Note that \\(N_Z(S)\\) is exactly the set of vertices in \\(R\\) incident to any red edge.



<a name="analysis"></a>
![Illustration of the analysis.](./analysis.png)

*Figure 2. For a set \\(S \subseteq L\\), we split its neighbors \\(U = N_L(S)\\) into \\(U_{\ell}\\) (the good set) and \\(U_h\\) (the bad set) based on a degree threshold \\(\tau\\).
Then, each \\(u\in U\\) shoots out red edges according to \\(N_L(u) \cap S\\) and \\(H\\).*



## Best case scenario {#best-case}

The best case scenario is that all edges from \\(S\\) go to distinct vertices, so \\(|U| = k|S|\\).
Then, for each \\(u\in U\\), within the local copy of the gadget \\(H\\), the left side has exactly one vertex from \\(S\\) (i.e., \\(|N_L(u) \cap S| = 1\\)).
\\(H\\) has degree \\(d\\), so \\(d\\) vertices of \\(N_R(u) \subseteq R\\) will be neighbors of \\(S\\) in the final product \\(Z\\).
That is, each \\(u\in U\\) shoots out \\(d\\) red edges, and we have \\(kd|S|\\) red edges in total.

The next best case scenario is that all red edges go to distinct vertices in \\(R\\).
Then, we would have exactly \\(|N_Z(S)| = kd|S|\\).

Notice that it is also fine if some \\(u\in U\\) has, say, \\(|N_L(u) \cap S| = 15\\) or any small constant.
Since \\(H\\) is a lossless expander, we expect it to contribute \\(15d\\) neighbors on the right.
In other words, as long as each \\(u\in U\\) contributes a factor of \\(d\\) and the red edges don't collide much, then
$$|N_Z(S)| \approx \sum_{u\in U} d \cdot |N_L(u) \cap S| = d \cdot |E(S,U)| = kd |S|.$$

However, even if \\(H\\) is the strongest lossless expander, only *small sets* can expand losslessly, so it is not true that \\(u\\) always gives a factor of \\(d\\).
For example, suppose \\(|N_L(u) \cap S| > 2D/d\\), since \\(H\\) has only \\(D\\) right-vertices, it is impossible to have \\(d \cdot |N_L(u) \cap S| > 2D\\) red edges from \\(u\\).

> *Observation.* \\(u \in U\\) contributes \\(\approx d \cdot |N_L(u) \cap S|\\) red edges only if \\(|N_L(u) \cap S| \ll D/d\\).

This motivates the general proof outline, which we describe next.



## Outline of the analysis

The analysis in all 3 papers have the following outline (see [Figure 2](#analysis) for illustration):

1. Pick a threshold \\(\tau\\), and split \\(U = N_L(S) \subseteq M\\) into \\(U_{\ell}\\) ("low-degree"; the good set) and \\(U_{h}\\) ("high-degree"; the bad set):
\\(U_{\ell} = \\{u\in U: |N_L(u) \cap S| \leq \tau\\}\\) and \\(U_h = U \setminus U_{\ell}\\).

2. **Left-to-middle analysis:** show that most edges coming out of \\(S\\) land in \\(U_{\ell}\\).
Equivalently, upper bound the number of edges in the induced subgraph \\(G_L[S \cup U_h]\\).

3. **Middle-to-right analysis:** show that the neighbors contributed from each gadget of \\(u\in U\\) have few collisions on the right.
Equivalently, upper bound the right average degree of the red edges (in fact, we need it to be close to 1 to get lossless expansion).

4. We choose the degree \\(d\\) of the gadget graph last.
In the left-to-middle analysis, we need \\(d \ll D/\tau\\) to get a factor \\(d\\) expansion from \\(U_{\ell}\\).
In the middle-to-right analysis, we will need a *lower bound* \\(d \gg \lambda\\), where \\(\lambda\\) will depend on the base graph.
Then, we check that
$$\lambda \ll d \ll D/\tau$$
can be satisfied.


**High-level intuition:**
For the left-to-middle analysis, 
if \\(G_L\\) is a sufficiently good expander, then we expect that the induced subgraph \\(G_L[S \cup U_h]\\) has small average degree.
But, since \\(U_h\\) all have high degree to \\(S\\), this subgraph must have very small left average degree, which means that most edges from \\(S\\) go to \\(U_{\ell}\\).


We expect \\(U_{\ell}\\) to shoot out many red edges, ideally close to \\(kd|S|\\).
For the middle-to-right analysis,
we need to prove that these red edges have few collisions on the right, or equivalently, the red subgraph (a subgraph of \\(G_R\\)) has small right average degree, which is indeed expected if \\(G_R\\) is a good expander.


# Unique-neighbor expanders [[HMMP24](#HMMP24)]  {#first-paper}

For the base graph, we use two bipartite Ramanujan graphs --- well-studied generalization of regular Ramanujan graphs.

> A \\((D_1,D_2)\\)-biregular graph is Ramanujan if the second eigenvalue of its adjacency matrix is at most \\(\sqrt{D_1-1} + \sqrt{D_2-1}\\).

In [[HMMP24](#HMMP24)], we prove the following result on the edge density of small subgraphs in near-Ramanujan bipartite graphs (which we believe to be independently interesting in spectral graph theory).

> **Theorem 2** (Informal; see Theorem 1.11 of [[HMMP24](#HMMP24)]).
> Let \\(G = (L, R, E)\\) be a \\((D_1, D_2)\\)-biregular near-Ramanujan graph.
> For any small enough subsets \\(S \subseteq L\\) and \\(T \subseteq R\\), let \\(d_1 = \frac{|E(S,T)|}{|S|}\\) and \\(d_2 = \frac{|E(S,T)|}{|T|}\\) be the left and right average degrees of the induced subgraph \\(G[S \cup T]\\).
> Then, $$(d_1 - 1) (d_2 - 1) \leq \sqrt{D_1 D_2} \cdot (1 + \mathrm{small}).$$

Theorem 2 is most useful when the bipartite graph is very unbalanced, say \\(D_1 \ll D_2\\).
For comparison, the [expander mixing lemma](https://en.wikipedia.org/wiki/Expander_mixing_lemma) (EML) gives
$$d_1 d_2 \leq (\sqrt{D_1-1} + \sqrt{D_2-1})^2 \approx D_2 + 2\sqrt{D_1 D_2}.$$


For the base graph, we pick \\(G_L\\) and \\(G_R\\) to be \\((k,D)\\)-biregular near-Ramanujan graphs.
The way we use Theorem 2 is simple: if any (small) subgraph in \\(G_L\\) or \\(G_R\\) has average degree \\(\gg \sqrt{kD}\\) on one side, then the other side must have average degree close to \\(1\\).

**Left-to-middle analysis**:
We set the degree threshold \\(\tau\\) to be \\(100 \sqrt{kD}\\).
Then, the induced subgraph \\(G_L[S \cup U_h]\\) has right degree at least \\(\tau\\).
Then, applying Theorem 2, we have that the left average degree \\(\overline{d}\\) of \\(G_L[S\cup U_h]\\) satisfies
$$(\overline{d}-1) (\tau-1) \leq \sqrt{kD} \Longrightarrow \overline{d} \leq 1.01.$$
Thus, on average only \\(1.01\\) out of \\(k\\) edges of each \\(v\in S\\) go to \\(U_h\\), meaning that roughly \\((k-1.01)|S|\\) edges go to \\(U_{\ell}\\), as desired.

**Middle-to-right analysis**:
We now look at the red edges coming from \\(U_{\ell}\\), which forms a subgraph of \\(G_R\\).
Let \\(T \subseteq R\\) be the subset of vertices incident to a red edge, which is exactly the neighbors of \\(S\\) in the final product \\(Z\\).
We know that each \\(u\in U\\) shoots out at least \\(d\\) red edges (e.g., exactly \\(d\\) in the [best case scenario](#best-case) mentioned earlier).
Thus, suppose we pick \\(d \geq 100 \sqrt{kD}\\), then again by Theorem 2, the average degree on the right side of the red subgraph is at most \\(1.01\\), i.e., very few  collisions on the right, as desired.
It seems that we're done!

**Did you catch the error?**
The vertices in \\(U_{\ell}\\) may have \\(|N_L(u) \cap S|\\) as large as \\(\tau = 100\sqrt{kD}\\).
But, we also set \\(d = 100\sqrt{kD}\\).
So, \\(\tau \ll D / d\\) is *not* satisfied (recall that we need this to get a factor \\(d\\) expansion from the gadgets).

Fortunately, the gadget \\(H\\) is a random graph, which (with high probability) has the property that any subset \\(A \subseteq [D]\\) of size \\(C D/d\\) has roughly \\(e^{-C} d|A|\\) unique-neighbors --- a factor of \\(e^{-C}\\).
Thus, this analysis shows that \\(S\\) has \\(\geq \gamma k d|S|\\) unique-neighbors for some tiny universal constant \\(\gamma > 0\\).


## The main question after this paper

Given the analysis above, it seems that to get an improvement, we need to beat what spectral expansion gives us.
Concretely, we want an explicit graph whose subgraphs are much sparser than what expander mixing lemma (EML) guarantees.
One interesting example is high-girth graphs.
We proved that high girth (or the absence of short *bicycles*) implies lossless expansion for all subsets of size at most \\(n^c\\), where \\(c\\) depends on the girth but does not exceed \\(1/2\\).
Thus, our unique-neighbor expanders have the extra guarantees that very small subsets expand losslessly --- see our paper and a nice follow-up work by Chen [[Che25](#Chen25)] for more details.

Of course, we want subsets of linear size to expand, thus the question of beating EML still remains.


# 0.6-vertex expanders [[HMLOZ25](#HLMOZ25)] {#second-paper}

Another intriguing example that beats expander mixing lemma (EML) is the result of Bourgain, Katz and Tao on the density of the point-line incidence graphs over a field \\(\mathbb{F}\\) --- at a high level, it improves \\(\sqrt{D}\\) (guaranteed by EML) to \\(D^{1/2-\varepsilon_0}\\) for some small \\(\varepsilon_0 > 0\\).
These graphs also have additional combinatorial properties, like being \\(4\\)-cycle free (because two points uniquely determine a line), which may potentially be exploited.

This led us to look at high-dimensional expanders (HDX), specifically the Ramanujan simplicial complexes of Lubotzky, Samuels and Vishne [[LSV05](#LSV05)], in which the local neighborhoods of vertices (a.k.a. links) are precisely these point-line incidence graphs.

Ultimately, we did not need the result of Bourgain, Katz \& Tao, because we realized that the HDX structure significantly improves the [middle-to-right analysis](#middle-to-right-hdx).
Nonetheless, I think it's worth mentioning that this is how we arrived at using HDX for the base graphs.


## Ramanujan complexes

For this blog post, we will only look at \\(2\\)-dimensional complexes.
For readers unfamiliar with [HDX](https://www.wisdom.weizmann.ac.il/~dinuri/courses/18-HDX/), think of it as a collection of triangles called "faces" on a vertex set --- each triangle is a set of 3 vertices.
If we put a \\(3\\)-clique for each triangle and remove duplicated edges, then we get a simple graph which is called the *\\(1\\)-skeleton*.
We denote this complex as \\(X = (X(0), X(1), X(2))\\), where \\(X(0)\\) is the vertex set, \\(X(1)\\) is the set of edges in the \\(1\\)-skeleton, and \\(X(2)\\) is the set of triangles.

For a vertex \\(v\in X(0)\\), the neighbors of \\(v\\) form a graph on \\(\deg(v)\\) vertices, where two vertices \\(w_1, w_2\\) are connected if \\(\\{v, w_1,w_2\\}\\) is a triangle in \\(X(2)\\).
This local graph is called the *link* of \\(u\\).

HDXs have the properties that
1. each link is an expander, and
2. the \\(1\\)-skeleton is an expander.

<!--
Note that if we randomly choose a set of triangles, the links will not even be connected.
It is quite magical that HDXs exist and can be constructed.
-->


**Heuristic calculations:**
Whenever we consider the link or the skeleton of the HDX, just assume that the second eigenvalue is at most \\(O(\sqrt{\mathrm{degree}})\\), thus any small subgraph has average degree \\(O(\sqrt{\mathrm{degree}})\\).

Then, we look at the construction of [[LSV05](#LSV05)],
parameterized by a prime power \\(q\\).
* Each vertex participates in \\(q^3\\) triangles.
* Every two distinct vertices are either part of \\(0\\) triangles or \\(q\\) triangles.
* As a result, the \\(1\\)-skeleton has degree \\(q^2\\) (degree \\(q^3\\) before removing duplicated edges, and each edge has multiplicity \\(q\\)).
* Each link is a bipartite graph on \\(q^2\\) vertices and has degree \\(q\\).

(The above are all approximations and correct up to constant factors, which we will ignore. See Theorem 3.4 of [[HLMOZ25](#HLMOZ25)] for precise parameters.)


## Face-vertex incidence graph as the base graph

For the base graph, we set \\(M\\) to be the vertices \\(X(0)\\), and \\(L\\) and \\(R\\) to be the triangles \\(X(2)\\).
The bipartite graphs \\(G_L\\) and \\(G_R\\) are the face-vertex incidence graphs, where edges between vertices and triangles are specified by containment.
Thus, each triangle has \\(3\\) vertices, so the left-degree \\(k=3\\).
Each vertex is contained in \\(q^3\\) triangles, so the right-degree \\(D = q^3\\).


**Left-to-middle analysis:**
Again, for \\(S \subseteq L\\) and \\(U = N_L(S) \subseteq M\\), we split \\(U\\) into \\(U_{\ell}\\) and \\(U_h\\) by setting a degree threshold \\(\tau\\).
Unfortunately, the face-vertex incidence graphs are not good expanders, so we cannot use the simple analysis in [the previous section](#first-paper).
Turns out, we can upper bound the edges between \\(S\\) and \\(U_h\\) by bounding the *triangle density*.

<!--
The analysis in [the previous section](#first-paper) turns out to be correct.
Unfortunately, this seems to be a coincidence and is false when we use higher-dimensional HDXs (for \\(k=5\\), we have \\(D = q^{10}\\) and we need \\(\tau = O(q^{6.5})\\)).
This is because the face-vertex incidence graphs are simply not good expanders.
-->


> **Theorem 3** (Triangle density of Ramanujan complexes; Lemma 1.2 and 3.11 of [[HLMOZ25](#HLMOZ25)]).
> For any small subset \\(U \subseteq X(0)\\), the number of triangles with all \\(3\\) vertices contained in \\(U\\) is at most \\(O(q^{3/2}) \cdot |U|\\).

> (For \\(k=5\\), the number of size-\\(5\\) faces with \\(3\\) or more vertices in \\(U\\) is at most \\(O(q^{6.5}) \cdot |U|\\).)

We will show a heuristic calculation [later](#triangle-density).

*Why is small triangle density useful?*
Recall that \\(S \subseteq L\\) is a subset of triangles in \\(X(2)\\), and \\(U_{\ell}, U_h\\) are subsets of vertices in \\(X(0)\\).
We want to show that not too many edges from \\(S\\) go to \\(U_h\\).
The triangles with all \\(3\\) vertices contained in \\(U_h\\) are precisely the vertices in \\(S\\) that have all \\(3\\) edges going to \\(U_h\\); let's call them \\(S_3 \subseteq S\\).
Thus, the triangle density bound shows that \\(|S_3|\\) must be at most \\(O(q^{3/2}) |U_h|\\).
But, \\(|U_h|\\) itself is small due to its large degrees.
This implies that \\(|S_3|\\) is small, and most vertices in \\(S\\) have at least \\(1\\) out of \\(3\\) edges going to \\(U_{\ell}\\).
This eventually gives us \\(\frac{1}{3}\\)-vertex expansion.

Concretely, we set the degree threshold \\(\tau\\) to be \\(\frac{1}{\delta}\\) times the triangle density for some small enough \\(\delta\\).
Then, \\(|E_L(S, U_h)|\\) is at most \\(3|S|\\) and at least \\(\frac{1}{\delta} q^{3/2} |U_h|\\), which means that \\(q^{3/2} |U_h| \leq 3\delta |S|\\).
But, the triangle density implies that \\(|S_3| \leq O(q^{3/2}) |U_h|\\).
Thus, we have \\(|S_3| \leq O(\delta) |S|\\) as desired.
Here, we need
$$d \ll D/\tau \ll \sqrt{D} = q^{3/2}.$$


## Middle-to-right analysis: structure of the HDX {#middle-to-right-hdx}

This part is where the advantage of HDX comes in.
Again, we think of the contribution of the gadget on each \\(u\in U\\) as shooting out "red" edges to \\(R\\), as in [Figure 2](#analysis).
We want to upper bound the number of collisions on the right.

Let's examine why \\(G_R\\) is not an expander.
Because of the structure of the HDX, two vertices in \\(X(0)\\) may be contained in many triangles.
Equivalently, two vertices in \\(M\\) may have many common neighbors in \\(R\\).
A priori, this might happen to the red edges, where the red edges coming out of two vertices have a lot of collisions.

<a name="red-edges"></a>
![Illustration of the red edges colliding.](./red.png)

*Figure 3.
Let \\(S \subseteq L\\) be the ones colored green. (These are drawn as cubes because [later](#third-paper) we will be using cubical complexes.)
We would like to upper bound the collisions of the red edges on the right.
Here, \\(u\\) has collisions with \\(v\\) and \\(w\\).
We must show that this cannot happen too often.*

Our main observation is that the red edges must be carefully (even adversarially) chosen for this to happen.
Intuitively, each vertex \\(u\in M\\) has \\(D = q^3\\) neighbors in \\(R\\), and they can be roughly split into buckets, where each bucket corresponds to a common neighborhood with another vertex \\(v\in M\\) --- that is, \\(N_R(u) \cap N_R(v)\\) corresponds to a specific bucket of \\(u\\)'s neighbors.
See [Figure 3](#red-edges) for an example of this common neighborhood structure.

In order for the bad scenario to happen, the red edges must be concentrated in one of the buckets.
Now, remember that our gadget \\(H\\) is a *random* graph, while these buckets are fixed.
So, it is unlikely that the red edges are concentrated like this.

This is exactly our intuition.

> **Lemma.** The gadget graph \\(H\\) is a graph on vertex set \\([D] \times [D]\\), and the vertices can be further partitioned into fixed buckets or *special sets* (determined by the structure of \\(X\\)).
> We show that in a random \\((d,d)\\)-biregular graph \\(H\\), the neighbors of any subset \\(A \subseteq [D] \\) in \\(H\\) are evenly spread out among these special sets.

> *Note:* This requires us to "place" the gadgets systematically according to the labels of the edges in the base graph.
> These labels are naturally provided by the Ramanujan complexes.


Let's do a rough calculation.

**Collision graph on \\(U\\):**
We construct a multigraph \\(C\\) on \\(U\\) as follows:
if \\(u,v\in U\\) have red edges that collide on the right (like in [Figure 3](#red-edges)),
then we add edges between \\(u\\) and \\(v\\) with the multiplicity being the number of collisions.
Our goal is to upper bound the number of edges in \\(C\\).

In the bad scenario mentioned earlier, \\(u\\) and \\(v\\) can have several red edges going to their common neighbors, which results in parallel edges in \\(C\\).
However, this won't happen too often due to the *spreadness* of \\(H\\).

Thus, in our heuristic calculation, we ignore the parallel edges.
Now, notice that \\(C\\) is a subgraph of the \\(1\\)-skeleton of \\(X\\) --- \\(u, v\\) can have a collision only if they are part of a triangle in \\(X(2)\\).

We now use the expansion of the HDX.
The \\(1\\)-skeleton of \\(X\\) has degree \\(q^2 = D^{2/3}\\) and second eigenvalue \\(\lambda = q = D^{1/3}\\), which means that the average degree of \\(C\\) must be at most \\(D^{1/3}\\).

Therefore, only a negligible fraction of the red edges have collisions if we choose
$$d \gg \lambda = D^{1/3} = q.$$


> If we use a spectral bipartite expander for \\(G_R\\), then we have that \\(C\\) is a subgraph of a degree-\\(D\\) graph with eigenvalue \\(\sqrt{D}\\).
> This requires us to choose \\(d \gg \sqrt{D}\\), which faces the same issue as the [previous section](#first-paper).

> *Key improvement.* Using an HDX, \\(C\\) is also a subgraph of a degree-\\(D\\) graph, but here each edge has multiplicity \\(q = D^{1/3}\\).
> At a high level, the spreadness of the random gadget allows us to ignore parallel edges, so essentially \\(C\\) is a subgraph of a degree-\\(D^{2/3}\\) graph with eigenvalue \\(D^{1/3}\\).
> This lets us choose \\(d\\) to be much smaller.


## Heuristic calculation for triangle density {#triangle-density}

Fix a subset \\(U \subseteq X(0)\\).
Consider the \\(1\\)-skeleton of \\(X\\), denoted \\(\widetilde{G}\\), and consider a vertex \\(u\in U\\).
If a triangle containing \\(u\\) also has its other \\(2\\) vertices \\(v,w\\) in \\(U\\), then \\(v,w\\) must be neighbors of \\(u\\), and moreover, \\(v,w\\) are connected in \\(\widetilde{G}\\).
In other words, \\(v,w\\) is an edge in the subgraph of the *link* of \\(u\\) induced by \\(N_{\widetilde{G}}(u) \cap U\\).

The \\(1\\)-skeleton has degree \\(q^2\\) and second eigenvalue \\(q\\).
Thus, a "typical" \\(u\in U\\) has roughly \\(q\\) neighbors in \\(U\\).
Its link is a graph on \\(q^2\\) vertices with degree \\(q\\) and second eigenvalue \\(\sqrt{q}\\).
Thus, a size-\\(q\\) subgraph in the link, particularly the one induced by \\(N_{\widetilde{G}}(u) \cap U\\), has at most \\(\sqrt{q} \cdot q = q^{3/2}\\) edges.

Thus, a typical \\(u\in U\\) contributes at most \\(q^{3/2}\\) triangles, and if all \\(u \in U\\) behave like this on average, then we get the desired bound of \\(q^{3/2} |U|\\).
We can show with some bucketing tricks that this is indeed correct.


## The main question after this paper

The above analysis shows that for a fixed \\(k\\), we get \\((1-\frac{2}{k})\\)-vertex expansion if the heuristic calculations work out.
Unfortunately, this stops at \\(k=5\\).
For \\(k=5\\), the triangle density is \\(q^{6.5}\\) (which is \\(D^{0.65}\\), worse than what EML would give), but it is saved by the middle-to-right analysis since the second eigenvalue of the \\(1\\)-skeleton is \\(q^3\\), so \\(q^{3} = \lambda \ll d \ll D/\tau = q^{3.5}\\) can be satisfied.
For \\(k=6\\) and above, this fails.

Instead of triangle density, we did try bounding the size-\\(j\\) face density --- the number of size-\\(k\\) faces with \\(j\\) or more vertices contained in \\(U\\).
This would give \\((1-\frac{j-1}{k})\\)-vertex expansion if things work out.
Rachel heroically did a lot of calculations for this, but it seems that the best we can get is \\(\frac{3}{4}\\) (so we didn't include it in our paper).

The problem seems to be that the higher-dimensional Ramanujan simplicial complexes are *not symmetric enough*.
The complex is \\(k\\)-partite, and the neighborhood structure of two vertices in parts \\(1\\) and \\(2\\) are drastically different from the neighborhood structure of two vertices in parts \\(1\\) and \\(k/2\\), for example.
This asymmetry shows up in the 1-skeleton as well.

It seems that what we need is a complex with **more symmetry**.



# Lossless expanders [[HLMRZ25](#HLMRZ25)] {#third-paper}

It turns out that **cubical complexes** are what we need.

## Cubical complexes

In an HDX, we have vertices, edges, triangles, tetrahedrons, and so on.
In a cubical complex, we have vertices, edges (1-dimensional subcubes), 2-dimensional subcubes, and so on.

We restrict to Cayley cubical complexes.

> **Definition** (Cubical generating set).
> Let \\(\Gamma\\) be a finite group, and \\(k\in \mathbb{N}\\).
> We say that \\(A_1, A_2,\dots, A_k \subseteq \Gamma\\) are *cubical generating sets* if they are closed under inverses, and
> * \\(A_i \cdot A_j = A_j \cdot A_i\\) for all \\(i \neq j\\),
> * \\(|A_1 \cdots A_k| = |A_1| \cdots |A_k|\\).

(Here, \\(A \cdot B\\) denotes the set \\(\\{a \cdot b: a\in A, b\in B\\}\\).)

Note that we require \\(A_1,\dots,A_k\\) to commute as sets while the elements do not necessarily commute.
In particular, for any \\(a_1 \in A_1\\) and \\(a_2 \in A_2\\), there exist unique elements \\(b_1\in A_1\\) and \\(b_2 \in A_2\\) such that \\(a_1 a_2 = b_2 b_1\\).

> **Definition** (Cubical complex).
> Given a finite group \\(\Gamma\\) and cubical generating sets \\(A_1,\dots,A_k \subseteq \Gamma\\), the Cayley cubical complex \\(X\\) is defined by:
> * vertex set \\(X(0) = \Gamma \times \mathbb{F}_2^k\\),
> * \\(k\\)-faces (or cubes) \\(X(k)\\) consisting of \\(2^k\\)-sized subsets of \\(X(0)\\) of the form \\(f = \\{(f_x, x)\\}_{x\in \mathbb{F}_2^k}\\) such that \\(f_x^{-1} f_y \in A_i\\) if \\(y = x \oplus e_i\\).

We also have \\(j\\)-dimensional subcubes in the cubical complex (for \\(j\leq k\\)), which I won't formally define here.
The definitions should be clear from the figure below.


<!--
We use the word "decorated" since the vertex set \\(X(0)\\) consists of \\(2^k\\) copies of \\(\Gamma\\), as opposed to the usual notion of Cayley graphs with a single copy of the group.
-->



<a name="cubical"></a>
![A cubical complex.](./cubical.png)

*Figure 4. A 3-dimensional cubical complex.
The vertex-face incidence graph we need for our base graph construction will be restricted to a linear code \\(C \in \mathbb{F}_2^k\\).
Here, the code \\(\\{000,011,110,101\\}\\) is highlighted.*


It is a simple exercise to show the following crucial properties:
* A cube is uniquely specified by two opposite corners. For example, \\((g,000)\\) and \\((h,111)\\) uniquely identify a 3-dimensional cube (i.e., there is at most 1 cube that contains these two points).
* More generally, a set of points \\( \\{(g_1, x_1), \dots, (g_m,x_m) \\}\\) uniquely identify a \\(k\\)-dimensional cube if for each coordinate \\(i\in[k]\\), there exists a pair \\(x_s, x_t\\) such that \\(x_s[i] \neq x_t[i]\\) ---
equivalently, \\(\cup_{t\in[m]} \mathrm{supp}(x_t \oplus x_1) = [k]\\).
For example, \\((g_1, 000), (g_2, 110), (g_3, 101)\\) uniquely identify a 3-dimensional cube.

See Lemma 3.3 of [[HLMRZ25](#HLMRZ25)] for the general version and the proof.


**Expanding cubical complex.**
It is straightforward to construct cubical complexes using abelian groups since all elements commute.
However, we need the complex to exhibit strong expansion, and it is well known that constant-degree abelian Cayley graphs cannot be expanders.

It turns out that we can construct cubical complexes with nice expansion properties based on the famous LPS Ramanujan graphs [[LPS88](#LPS88)].
In fact, we only need basic properties of the generating sets of these Cayley graphs, while using the (highly non-trivial) fact that they are Ramanujan as a black box.
Check out Section 4 of [[HLMRZ25](#HLMRZ25)] for a mostly self-contained exposition.


## Coded face-vertex incidence graph

**Notation.**
We will assume that \\(|A_1| = |A_2| = \cdots = |A_k| = p\\) for simplicity.

Let's go back to our original motivation.
We want complexes with more symmetry.
But even for a cubical complex, the interactions between parts \\(000\\) and \\(001\\) are very different than those between parts \\(000\\) and \\(111\\).
For example, one point in \\(\Gamma \times \\{000\\}\\) and one in \\(\Gamma \times \\{111\\}\\) has at most 1 cube containing them.
However, one point in \\(\Gamma \times \\{000\\}\\) and one in \\(\Gamma \times \\{001\\}\\) can have \\(p^2\\) distinct cubes containing them.

> *Key idea*: we restrict to a code \\(C \subseteq \mathbb{F}_2^k\\) of distance close to \\(1/2\\).
> That is, we use the face-vertex incidence graph between \\(L = X(k)\\), the \\(k\\)-faces, and \\(M = \Gamma \times C\\), the subset of \\(X(0)\\) restricted to \\(C\\).

We call this a "coded" face-vertex incidence graph.
See [Figure 4](#cubical) for an example.

In our paper, we choose the Hadamard code so that the distance is exactly \\(k/2\\).
In fact, any \\(\delta\\)-balanced code for \\(\delta < 0.1\\) will work and will actually improve the dependency between \\(\varepsilon\\) and the degree, but we did not optimize for this in our paper.

Now, each pair \\(\Gamma \times \\{x\\}\\) and \\(\Gamma \times \\{y\\}\\) for \\(x,y\in C\\) look roughly the same.
We have the desired symmetry!


## Heuristic calculation for subcube density

For the left-to-middle analysis, we will study the *subcube density*, similar to the [triangle density](#triangle-density) analysis in the previous paper.

Let's focus on \\(k=3\\), and a code \\(C = \\{000, 011, 101, 110\\}\\).
Given a small subset \\(U \subseteq \Gamma \times C\\), how many cubes have \\(4\\) vertices in \\(U\\)?
That is, we want to bound
$$|\{f \in X(3): |f \cap U| = 4\}|.$$

Denote \\(U_x := U \cap (\Gamma \times \{x\})\\).
Consider the bipartite graph between \\(\Gamma \times \\{000\\}\\) and \\(\Gamma \times \\{110\\}\\).
Two vertices \\((g, 000)\\) and \\((h, 110)\\) are connected if there exist \\(a_1 \in A_1\\) and \\(a_2 \in A_2\\) such that \\(h = ga_1 a_2\\).
This bipartite graph has degree \\(p^2\\) and second eigenvalue roughly \\(p\\).
Thus, a typical vertex \\(u\in U_{000}\\) has roughly \\(p\\) neighbors in \\(U_{110}\\).

Then, \\(u \in U_{000}\\) and a neighbor in \\(U_{110}\\) uniquely determines a subcube in coordinates \\(1\\) and \\(2\\), and there are \\(p\\) ways to extend it to a full \\(3\\)-dimensional cube.
Thus, we get a bound of \\(p^2 |U|\\).

**We can do better!**
By our choice of the code \\(C\\), any cube \\(f\\) is uniquely identified by any \\(3\\) points in \\(f \cap (\Gamma \times C)\\).
For example, \\((g, 000)\\), \\((ga_1a_2, 110)\\) and \\((ga_1 a_3, 101)\\) uniquely specify a cube \\(f\\), and in particular, there exist unique \\(a_2' \in A_2\\) and \\(a_3' \in A_3\\) such that \\((ga_2' a_3', 011)\in f\\).

Let's assume that \\(a_2' = a_2\\) and \\(a_3' = a_3\\) for simplicity.
A typical \\(u \in U_{000}\\) has \\(p\\) neighbors in \\(U_{110}\\), \\(U_{101}\\) and \\(U_{011}\\).
Any cube containing \\(u\\) is specified by \\((a_1, a_2, a_3)\\), so bounding the number of cubes containing \\(u\\) and also with vertices in \\(U_{110}, U_{101}, U_{011}\\) is equivalent to the following question:

> For a set of \\(3\\)-tuples \\(T\\), suppose \\(N_{12} = |\\{(a_1, a_2): (a_1,a_2,a_3)\in T\\) for some \\(a_3\in T\\}|\\) and \\(N_{13}, N_{23}\\) defined similarly, how large can \\(T\\) be?

The answer is \\(|T| \leq \sqrt{N_{12} N_{23} N_{13}}\\).
This is in fact a special case of the *[Loomis-Whitney inequality](https://en.wikipedia.org/wiki/Loomis%E2%80%93Whitney_inequality)*.
Here, we give a simple proof using an entropic argument. For the uniform distribution over \\(T\\), we have \\(H(a_1,a_2,a_3) = \log|T|\\), while by assumption \\(H(a_i, a_j) \leq \log N_{ij}\\) for \\(i < j\\).
Then, the [Shearer's inequality](https://en.wikipedia.org/wiki/Shearer%27s_inequality) states that
$$\log |T| = H(a_1, a_2, a_3) \leq \frac{1}{2} \sum_{i<j} H(a_i, a_j) \leq \frac{1}{2} (\log N_{12} + \log N_{13} + \log N_{23}).$$

This gives a bound of \\(p^{3/2} |U|\\), much better than the naive \\(p^2|U|\\) bound!

We apply the same idea to larger \\(k\\) and \\(C \subseteq \mathbb{F}_2^k\\) being the Hadamard code.
We get

> **Theorem** (Subcube density; Lemma 3.12 of [HLMRZ25]).
> For any small subset \\(U \subseteq \Gamma \times C\\), we have
> $$\left|\\{f \in X(k): |f \cap U| \geq 2\sqrt{k}\\}\right| \leq O(p^{5k/8}) |U| = O(D^{5/8}) |U|.$$

We note that the naive bound gives \\(D^{3/4}|U|\\), which falls just short of what we need.



## Putting things together

**Left-to-middle analysis:**
Given the subcube density, we pick the degree threshold \\(\tau = D^{5/8}\\).
Then, with the same calculation as before, it follows that \\(1 - \frac{2\sqrt{k}}{k}\\) fraction of edges from \\(S\\) go to the good set \\(U_{\ell}\\).

We simply need to pick \\(k = O(1/\varepsilon^2)\\) to get \\(1-\varepsilon\\).

**Middle-to-right analysis:**
This part is basically the same as the [calculation for HDX](#middle-to-right-hdx), so we will be brief here.
The same intuition applies here: that we can ignore edge multiplicities in the collision graph.
Because the Hadamard code has distance \\(k/2\\), the bipartite graph between any two parts has degree \\(p^{k/2}= D^{1/2}\\) and second eigenvalue \\(\lambda = D^{1/4}\\).

Thus, we need the degree \\(d\\) of the gadget graph \\(H\\) to satisfy
$$\lambda \ll d \ll D/\tau.$$

We are done!


# References

<a name="AC02"></a>
[AC02]
Noga Alon and Michael Capalbo.
Explicit unique-neighbor expanders.
In *Proceedings of the 43rd Annual IEEE Symposium on Foundations of Computer Science*, pages 73–79, 2002.

<a name="Chen25"></a>
[Che25]
Yeyuan Chen.
Unique-neighbor Expanders with Better Expansion for Polynomialsized Sets.
In *Proceedings of the 2025 Annual ACM-SIAM Symposium on Discrete Algorithms (SODA)*, pages 3335–3362. SIAM, 2025.

<a name="HLMOZ25"></a>
[HLMOZ25]
Jun-Ting Hsieh, Ting-Chun Lin, Sidhanth Mohanty, Ryan O’Donnell, and Rachel Yun Zhang.
Explicit Two-Sided Vertex Expanders Beyond the Spectral Barrier.
In *Proceedings of the 57th Annual ACM Symposium on Theory of Computing*, 2025.

<a name="HLMRZ25"></a>
[HLMRZ25]
Jun-Ting Hsieh, Alexander Lubotzky, Sidhanth Mohanty, Assaf Reiner, Rachel Yun Zhang.
Explicit Lossless Vertex Expanders
*arXiv preprint arXiv:2504.15087*, 2025.


<a name="HMMP24"></a>
[HMMP24]
Jun-Ting Hsieh, Theo McKenzie, Sidhanth Mohanty, and Pedro Paredes.
Explicit two-sided unique-neighbor expanders.
In *Proceedings of the 56th Annual ACM Symposium on Theory of Computing*, pages 788–799, 2024.

<a name="KY24"></a>
[KY24]
Dmitriy Kunisky and Xifan Yu.
Computational hardness of detecting graph lifts and certifying lift-monotone properties of random regular graphs.
In *Proceedings of the 65th Annual IEEE Symposium on Foundations of Computer Science*, pages 1621-1633, 2024.

<a name="LH22"></a>
[LH22]
Ting-Chun Lin and Min-Hsiu Hsieh.
Good quantum LDPC codes with linear time decoder from lossless expanders.
*arXiv preprint arXiv:2203.03581*, 2022.



<a name="LPS88"></a>
[LPS88]
Alexander Lubotzky, Ralph Phillips, and Peter Sarnak.
Ramanujan graphs.
*Combinatorica*, 8:261–277, 1988.

<a name="LSV05"></a>
[LSV05]
Alexander Lubotzky, Beth Samuels, and Uzi Vishne.
Explicit constructions of Ramanujan complexes of type  \\(\tilde{A_d}\\).
*European Journal of Combinatorics*, 26(6):965–993, 2005.

<a name="MOP20"></a>
[MOP20]
Sidhanth Mohanty, Ryan O’Donnell, and Pedro Paredes.
Explicit near-Ramanujan graphs of every degree.
In *Proceedings of the 52nd Annual ACM SIGACT Symposium on Theory of Computing*, pages 510–523, 2020.

<a name="RSV19"></a>
[RSV19]
Nithi Rungtanapirom, Jakob Stix, and Alina Vdovina.
Infinite series of quaternionic 1-vertex cube complexes, the doubling construction, and explicit cubical Ramanujan complexes.
*International Journal of Algebra and Computation*, 29(06):951–1007, 2019.