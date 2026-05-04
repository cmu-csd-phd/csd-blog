+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "Fair allocations and Nash social welfare"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2025-05-02

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Theory"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
# Consider these similar to keywords specified for a research paper.
tags = ["Nash Social Welfare", "Approxiimation Algorithms","Fairness", "Optimization", "Convex Programming", "Fair Allocation"]

[extra]
author = {name = "Madhusudhan Reddy Pittu", url = "https://mathrulestheworld.github.io" }
# The committee specification is  a list of objects similar to the author.
committee = [
    {name = "Ryan O'Donnell", url = "https://www.cs.cmu.edu/~odonnell/"},
    {name = "Daniel Sleator", url = "https://www.cs.cmu.edu/~sleator/"},
    {name = "Noah Singer", url = "https://noahsinger.org"}
]
+++

>How do we allocate items among individuals with different preferences in a way that is both *fair* and *efficient?* 
<p></p>

Striking this balance is a fundamental challenge in economics and game theory, with implications ranging from inheritance division and divorce settlements to resource allocation and scheduling in computing. 


In this blog, I will first introduce standard fairness and efficiency notions for both divisible and indivisible items. Then, I will explore Nash social welfare, its fascinating properties, and its connection to Fisher markets. Finally, I will discuss the current algorithmic literature regarding approximability of Nash social welfare, which includes my publication at SODA 2024 \[[Brown, Laddha, **Pittu**, Singh, 2024](https://epubs.siam.org/doi/abs/10.1137/1.9781611977912.52)\].


# Introduction

In the fair division setting we are going to discuss, the items are desirable *resources* generally also referred to as *goods*. This is the case in inheritance division and resource allocation in computing. 
More generally, the items can be undesirable in which case they are referred to as *chores* or *bads*. For example, in the case of scheduling tasks to unrelated parallel machines, the tasks are chores. 

In an allocation scenario, we have a set of \\(n\\) agents and \\(m\\) goods denoted by \\(N\\) and \\(M\\) respectively. Every agent \\(i\in N\\) has a preference over bundles of goods in \\(M\\), where a bundle is some (fractional) subset of goods. The preference of each agent \\(i \in N\\) is represented by a valuation function \\(v_i : [0,1]^M \rightarrow \mathbb{R}_{\geq 0}\\) where \\([0,1]^M\\) is the space of all \\(m\\)-dimensional vectors with entries indexed by the goods and values in the range \\([0,1]\\). To reflect the desirability of the goods, the valuations are always *monotone*; i.e., \\(v_i((x_1,\dots,x_m))\leq v_i((y_1,\dots,y_m)) \hspace{0.25em}\\) when \\(x_j\leq y_j\\) for all \\(1\leq j\leq m \\). Simply put, adding more goods makes agents happier. Assume also that \\(v_i(\emptyset)=0\\) for every \\(i\in N\\).

An allocation is a partition of the goods in \\(M\\) into \\(n\\) bundles, each bundle corresponding to an agent. More formally, we represent an allocation by a *column stochastic* matrix:
$$x\in [0,1]^{N\times M}, \hspace{0.25em} \sum\_{i \in N}x\_{i,j}=1 \quad \forall j \in M.$$ When the goods are indivisible, the allocation is integral; i.e., \\(x\_{i,j}\in \\{0,1\\}\\). In this case, we will use \\(x_i\\) also as the set of goods allocated to agent \\(i\\). 

The valuations are said to be *additive* if \\(v_i(x_i)=\sum\_{j\in M}x\_{i,j}v_i(\\{j\\})\\). Let us use \\(v\_{i,j}\\) as short for \\(v_i(\\{j\\})\\). For example, look at [Figure 1](#example).



## Fairness and Efficiency {#fair-efficient}

### Fairness
While there is no single universally agreed-upon notion of fairness, these notions generally fall into two categories, either *envy*-based or *share*-based. We will focus our attention on the former notion. An allocation is said to be *envy-free* (EF) if every agent prefers their own bundle over bundles of other agents. 

> **Definition 1.** (EF) An allocation \\(x\\) is said to be envy-free if for any two agents \\(i,k \in N\\), 
$$v_i(x_i)\geq v_i(x_k).$$
<p></p>

It is easy to see that when goods are divisible and finite, envy-free allocations exist: distribute every good uniformly to every agent. Since all bundles are identical, there cannot be envy. This fact is non-trivial when the set of goods is infinite even with additive valuations. An example of this case is the popular [cake cutting](https://www.cs.cmu.edu/~arielpro/15896s16/docs/paper10.pdf) problem.

 When goods are indivisible, an envy-free allocation may not always exist. For example, if there is only one good and two agents who both value it, any integral allocation will leave one agent empty-handed and envious of the other. 

A relaxation of envy-freeness to the case of indivisible items is *envy-freeness up to one good* (EF1). An allocation is said to be envy-free up to one good if every agent prefers their own bundle up to removal of **some** good in a different bundle.
> **Definition 2.** (EF1) An allocation \\(x\\) is said to be envy-free up to one good if for any two agents \\(i,k \in N\\), there **exists** an item \\(j\in x_k\\) such that  
$$v_i(x_i)\geq v_i(x_k\backslash \\{j\\}).$$
<p></p>


 Notice that in the previous example with a single good and two agents, any allocation that gives the good completely to one of the agents is EF1. In fact, EF1 allocations are always guaranteed to exist \[[LMMS04](https://dl.acm.org/doi/10.1145/988772.988792)\] and such an allocation can be found in polynomial time. When the valuations are additive, a simple round-robin scheme where agents take turns in a fixed order to pick their favorite unallocated item gives an EF1 allocation. 

A stronger version of EF1 is *envy-freeness up to any good* (EFX). An allocation is said to be envy-free up to any good if every agent prefers their own bundle up to removal of **any** good in a different bundle. 
> **Definition 3.** (EFX) An allocation \\(x\\) is said to be envy-free up to any good if for any two agents \\(i,k \in N\\) and **any** item \\(j\in x_k\\), 
$$v_i(x_i)\geq v_i(x_k\backslash \\{j\\}).$$
<p></p>

It is not known if EFX allocations always exist! No counter example for general monotone valuations or proof of existence for the simpler case of additive valuations is known. An excellent survey on the fair division of indivisible goods can be found [here](https://arxiv.org/pdf/2202.07551). 
> **Open problem 1.** Do EFX allocations exist?
<p></p>
Since we do not know if EFX allocations exist, let us assume EF and EF1 as the default notion of fairness for divisible and indivisible items respectively. 

### Example {#example}
![Example](valuations.png)
*Figure 1: An example with two agents and three goods with additive valuations. Alice is a sweet-tooth vegetarian, and Bob is a gym bro who cheats on his diet sometimes.*

A few example integral allocations and their fairness properties of the instance in [Figure 1](#example) are mentioned below:
1. **Envy-free**: Alice gets Ice cream, and Bob gets Chicken and Broccoli. Both of them prefer the goods they received over the goods the other person received. 
2. **EFX**: Alice gets Broccoli and Ice cream, and Bob gets Chicken. Alice is not envious of Bob, but Bob prefers Alice's bundle just a bit more than his. However, this envy can be removed if he ignores any one item that Alice received. 
3. **EF1**: Alice gets Broccoli, and Bob gets Chicken and Ice cream. Bob is not envious of Alice, but Alice just likes her Ice cream too much. However, this envy can be removed if she ignores that Ice cream, just like we all should. 
### Efficiency {#efficient}
The standard notion of efficiency is *Pareto optimality* (PO). An allocation \\(x\\) is said to be *Pareto dominated* by allocation \\(y\\) if switching from \\(x\\) to \\(y\\) makes no agent less happier and some agent strictly happier. More formally, \\(v_i(y_i)\geq v_i(x_i)\\) for every agent \\(i\in N\\) and \\(v_k(y_k)> v_k(x_k)\\) for some agent \\(k\in N\\).  

An allocation \\(x\\) is said to be Pareto optimal with respect to a set \\(A\\) of allocations if it is not Pareto dominated by any other allocation \\(y\in A\\). Unless otherwise specified, \\(A\\) is the set of integral allocations if \\(x\\) is integral and fractional otherwise. 

The existence of Pareto optimal solutions follows from the boundedness and compactness of valuations and the space of allocations respectively. One way to obtain a solution that is Pareto optimal is to find an allocation \\(x\\) that maximizes a *social welfare function* \\(w\\) of your choice. Social welfare functions aggregate the valuations of all the agents into a single number such that \\(w(y)> w(x)\\) iff allocation \\(y\\) Pareto dominates allocation \\(x\\). Popular examples of such welfare functions are: 
- Utilitarian welfare: welfare is the sum of valuations, \\(w(x)=\sum\_{i\in N}v_i(x_i)\\),
- Egalitarian welfare: welfare is the minimum of valuations, \\(w(x)=\min\_{i\in N}v_i(x_i)\\),
- Nash welfare: welfare is the geometric mean of valuations, \\(w(x)=\prod\_{i\in N}v_i(x_i)^{1/n}\\).

Going back to Alice and Bob in [Figure 1](#example), more example allocations are mentioned below:
 1. **Pareto Dominated**: Alice gets Chicken and Broccoli, and Bob gets Ice cream. Swapping their bundles makes both of them much happier. 
 2. **Maximum Utility**: Alice gets Broccoli and Ice cream, and Bob gets Chicken. The total of valuations is maximized, which is \\(30+10=40\\). Notice that in such an allocation scheme, Bob can report his valuations in a different scale where all his valuations are multiplied by a factor of \\(10\\) and steal all the goods.
 3. **Egalitarian Paradise**: Alice gets Ice cream, and Bob gets Chicken and Broccoli. The minimum valuation is maximized, which is \\(18\\). This time, Alice can report her valuations in a different scale where all her valuations are multiplied by a factor of \\(0.1\\) and steal the broccoli from Bob.
 
 Notice that scaling the valuations will not affect the allocation maximizing the Nash welfare. 
# Nash Social Welfare and Fisher Markets 
 Henceforth, assume that the valuation function is additive unless stated otherwise. In the [previous section](#fair-efficient), we defined notions of fairness and efficiency and discussed their existence individually. We also defined the Nash social welfare (NSW) as the geometric mean of the valuations of the agents. We will prove some properties of the NSW objective in this section. 
 
 We saw that allocations that maximize the utilitarian welfare or the egalitarian welfare can be very unfair.
 Can we balance both fairness and efficiency? I will discuss answers to the following two questions: 
 > 1. Is there a fractional allocation that is both EF and PO?
 > 2. Is there an integral allocation that is EF1 and PO?
 <p></p>
Yes, and Yes! In fact, the allocation that maximizes NSW satisfies the fairness and efficiency conditions in both cases. To be more clear, the fractional allocation that maximizes the NSW is both EF and PO with respect to fractional allocations, and the integral allocation that maximizes the NSW is both EF1 and PO with respect to integral allocations. We will first prove the integral case and then argue that the proof for the fractional case should follow using a limiting argument. 

> **Lemma 1.** An integral allocation maximizing NSW is both EF1 and PO.
 <p></p>
 
**Proof of Lemma 1.** The PO property follows from the fact that the solution maximizes a social welfare function. Let \\(x\\) be the allocation optimizing NSW. Suppose that allocation \\(x\\) is not EF1: then there exists agents \\(i,k \in N\\) such that agent \\(i\\) envies agent \\(k\\) even after removing any good \\(j\in x_k\\). This condition can be written as 
$$v_i(x_i) < v_i(x_k\backslash \\{j\\})=v_i(x_k)-v\_{i,j} \quad \forall j\in x_k .$$ We will show in that case, that there exists a good in \\(x_k\\) that can be given to agent \\(i\\) such that the NSW objective increases. Intuitively, if there is a good \\(j\in x_k\\) that is not so valuable for agent \\(k\\) but very valuable to agent \\(j\\), then moving this good from agent \\(k\\) to agent \\(i\\) should improve the valuation of agent \\(i\\) while not decreasing the valuation of agent \\(k\\) very much. Let us define this good as \\(j^\ast\in \argmax\_{j\in x_k}v_\{i,j\}/v_\{k,j\}\\). We consider the difference in Nash social welfare (raised to the \\(n^{th}\\) power) between the new allocation obtained by giving good \\(j^\ast\\) to agent \\(i\\) and allocation \\(x\\). This quantity is 
\begin{align}
v_i(x_i \cup\\{j^\ast\\})\cdot v_k(x_k\backslash \\{j^\ast\\})-v_i(x_i)\cdot v_k(x_k)&= (v_i(x_i)+v\_{i,j\ast})\cdot(v_k(x_k)-v\_{k,j\ast})-v_i(x_i)\cdot v_k(x_k) \nonumber \newline 
&= v_k(x_k)\cdot v\_{i,j^\ast}-(v_i(x_i)+v\_{i,j\ast})\cdot v\_{k,j\ast} \nonumber
\end{align}
times the product of the valuation of the remaining agents, which we will assume to be equal to \\(1\\). Using the EF1 violation assumption, we have \\(v_i(x_i)+v\_{i,j^\ast}< v_i(x_k)\\) and using the definition of \\(j^\ast\\), we have \\(v\_{i,j^\ast}/v\_{k,j^\ast} \geq v_i(x_k)/v_k(x_k)\\) because \\(v_i(x_k)/v_k(x_k)\\) is a weighted average of the ratios \\(v\_{i,j}/v\_{k,j}\\) for \\(j\in x_k\\) . Combining both the inequalities gives $$v_k(x_k)\cdot v\_{i,j^\ast}-(v_i(x_i)+v\_{i,j^\ast})\cdot v\_{k,j^\ast}> v_k(x_k)\cdot v\_{i,j^\ast}- v_i(x_k)\cdot v\_{k,j^\ast} \geq 0,$$ contradicting the maximality of \\(x\\). \\(\ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \  \square\\)

For more properties of NSW for indivisible items, look at \[[CKMPSW19](https://www.cs.toronto.edu/~nisarg/papers/mnw.ec16.pdf)\].

For the divisible case, imagine a sequence of instances where the goods are successively subdivided into finer and finer sub-goods. Consider the integral allocation of these sub-goods that maximizes the NSW. Using Lemma 1 for these instances tells us that the allocation is EF1 and PO. The 'envy gap' between any two agents is at most the valuation of a single sub-good which converges to zero in the limit. 

For divisible items, allocations that are EF and PO can be better understood through [*market equilibria*](https://en.wikipedia.org/wiki/Competitive_equilibrium). In the next section, I will introduce the linear utilities case of *Fisher markets* and its connection to NSW. 

## Fisher Markets {#fisher-markets}

In a Fisher market, there is a set \\( M \\) of divisible goods and a set \\( N \\) of agents or *buyers* \\( i \in N \\), each buyer with a valuation function \\( v_i \\). Each buyer enters the market with an *endowment* (or budget) \\( b_i > 0 \\). Each good \\( j \in M \\) has a price \\( p_j \\), and the price of a bundle represented by \\( (y_1,\dots,y_m)\\) is \\( p(y) = \sum_{j \in M} p_j y_j \\). 
Given market prices \\(p\\), the *demand set* \\(D_i(p)\\) of agent \\( i \in N \\) is the set of affordable bundles that maximize the agent's valuation. More formally,
$$
D_i(p) = \arg\max_{p(y) \leq b_i} v_i(y)
$$

> **Definition 4.** (Market equilibrium) Given a Fisher market, the pair \\((x,p)\\) of allocation and prices is a *Fisher market equilibrium* if the following criteria are met:  
> - **Market clearing:** Every item \\(j\in M\\) is either priced at zero or completely sold, that is, \\(p_j(\sum_{i\in N}x_{i,j}-1)=0\\).  
> - **Budget exhaustion:** Buyers spend all their money; i.e., \\(\sum_{j\in M}p_jx_{i,j}=b_i\\).  
> - **Demand allocation:** Every buyer gets the best bundle they can afford; i.e., \\(x_i \in D_i(p)\\).  
<p></p>

Roughly put, at market equilibrium, demand equals supply. It turns out that market equilibria always exist even for general monotone valuations.  
The proof uses the non-algorithmic tool of [Sperner's lemma](https://en.wikipedia.org/wiki/Sperner%27s_lemma) (see the [Wiki page](https://en.wikipedia.org/wiki/Fisher_market) and [Scarf-paper](https://www.jstor.org/stable/1909383) for more details). When the valuation function is additive, market equilibrium can be captured as an optimal primal-dual solution pair of a convex program called the [Eisenberg-Gale](https://www.jstor.org/stable/2237130) (EG) program. The EG program is as follows:
\begin{align}
\max:& \sum_{i\in N}b_i\log v_i(x) \nonumber \newline 
\textnormal{s.t.} \quad &v_i(x)= \sum_{j\in M}x_{i,j}v_{i,j} \quad \forall i\in N \nonumber \newline 
 &\sum_{i\in N}x_{i,j}\leq 1, \quad \forall j \in M \nonumber \newline
 &x\geq 0. \nonumber
\end{align}
If the Lagrangian variables corresponding to the conditions  \\(\sum_{i\in N}x_{i,j}\leq 1\\) are \\(p_j\\), then the optimal pair \\((x,p)\\) satisfies the market equilibrium conditions mentioned in Definition 4 using the [KKT](https://en.wikipedia.org/wiki/Karush–Kuhn–Tucker_conditions) optimality conditions. For a detailed proof, look at [Chapter 5, Algorithmic Game Theory](https://www.cs.cmu.edu/~sandholm/cs15-892F13/algorithmic-game-theory.pdf). The EG program can be used to obtain market equilibria for an even more general class of concave, homogeneous, and continuous valuations (see [Lecture notes](http://www.columbia.edu/~ck2945/files/ai_games_markets/lecture_note_7_fair_division.pdf)).

What is the connection to NSW? When the buyers have budgets all equal to \\(1\\), the market equilibrium that EG computes is simply the NSW-maximizing allocation! This equilibrium is also called the *competitive equilibrium from equal incomes* for this reason.

The EF property of the NSW maximizing solution can now be justified easily. Since every agent spends \\(1\\) unit of money, the bundles of other agents are affordable. From the demand allocation property, each agent receives the best possible bundle they can afford. This means there is no envy.
# Algorithmic Aspects and Generalizations
One can efficiently find a fractional allocation that is both EF and PO by solving the EG convex program. In fact, flow-based [combinatorial algorithms](https://ieeexplore.ieee.org/stamp/stamp.jsp?tp=&arnumber=1181963) to solve the EG program are known. 

What about the integral case? Can we efficiently find an integral allocation that is EF1 and PO? Unfortunately, even though the NSW-maximizing allocation is guaranteed to have this property, finding such an allocation is NP-hard \[[DS14](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=2410766)\].
<!---->
<!-- This is later improved to APX hardness \[[Lee15](https://www.sciencedirect.com/science/article/pii/S0020019017300212)\].-->
> **Open problem 2.** Can an EF1 and PO integral allocation found in polynomial time?
<p></p>

However, a pseudopolynomial time algorithm has been found in \[[BKV18](https://dl.acm.org/doi/10.1145/3219166.3219176)\] that computes an EF1 and PO allocation. 

Putting fairness aside, several works \[[CG15](https://dl.acm.org/doi/10.1145/2746539.2746589), [CGD+17](https://dl.acm.org/doi/10.1145/3033274.3085109), [AGSS16](https://www.semanticscholar.org/paper/Nash-Social-Welfare%2C-Matrix-Permanent%2C-and-Stable-Anari-Gharan/269dc168d29cd7ab06e67e9ce0bf287c4b120d9d), [BKV18](https://dl.acm.org/doi/10.1145/3219166.3219176)\] have studied the approximability of the NSW objective, obtaining constant factor approximations. On the lower-bound side, APX-hardness was shown in \[[Lee15](https://www.sciencedirect.com/science/article/pii/S0020019017300212)\].  

Two possible directions to generalize the NSW problem are:
1. Extend the valuation functions to a more general class,
2. Generalize the Social welfare function.

The most popular class of valuations that extends additive valuations is the class of [*submodular functions*](https://en.wikipedia.org/wiki/Submodular_set_function). It captures the diminishing returns property of agent valuations. Constant approximations to NSW maximization with submodular valuations are known \[[LV21](https://ieeexplore.ieee.org/document/9719864), [GHLVV23](https://dl.acm.org/doi/10.1145/3564246.3585255)\].

There has been recent interest in the generalization of NSW to an asymmetric version also called the *weighted Nash social welfare* (WNSW), which is a weighted geometric mean of the valuations of the agents; i.e., 
$$\mathrm{WNSW}(x)= \prod\_{i\in n}(v_i(x))^{w_i} $$
 for some fixed weights \\(w_i\geq 0\\) such that \\(\sum\_{i\in N}w_i=1\\). Going back to the [Fisher markets section](#fisher-markets), the fractional allocation that maximizes the WNSW is the market equilibrium when the buyers \\(i\in N\\) arrive with budget \\(n\cdot w_i\\). This suggests a generalization of envy when agents have different budgets, which I will refrain from discussing.

 **Our Work:** The first work to study the WNSW problem for additive valuations case is \[[Brown, Laddha, **Pittu**, Singh](https://epubs.siam.org/doi/abs/10.1137/1.9781611977912.52)\]. We provide a \\( 5 \cdot \exp\left(2 \cdot D_{\mathrm{KL}}(w \\\| \mathbf{1}/n)\right) \\)-approximation for the WNSW objective, where \\( D_{\mathrm{KL}} \\) denotes the Kullback–Leibler divergence.
 The main idea is to obtain two different relaxations of the problem: one convex and the other non-convex. The convex relaxation is used to obtain a fractional allocation and the non-convex relaxation is used to round it (similar to the [pipage rounding technique](https://www.semanticscholar.org/paper/Pipage-Rounding%3A-A-New-Method-of-Constructing-with-Ageev-Sviridenko/a2e025e9bb755d84b4171f34cac013d5a484ff80)). The approximation ratio is essentially the difference between the convex and the non-convex objectives. 

Recently, a constant approximation to the WNSW problem with additive valuations has been obtained by \[[FL24](https://drops.dagstuhl.de/storage/00lipics/lipics-vol297-icalp2024/LIPIcs.ICALP.2024.63/LIPIcs.ICALP.2024.63.pdf)\], which was later generalized to the submodular valuations case in \[[FHLR24](https://arxiv.org/abs/2411.02942)\].

## Conclusion

The Nash social welfare objective offers a compelling way to balance fairness and efficiency in allocation problems. Its connection to market equilibria provides strong structural guarantees in the divisible setting, while the indivisible case presents ongoing algorithmic challenges. Recent advances, including our work on the weighted variant, highlight both the versatility of the framework and the potential for further progress in understanding and approximating fair outcomes.

# Bibliography

[EG, 1959] Eisenberg, Edmund, and David Gale. “Consensus of Subjective Probabilities: The Pari-Mutuel Method.” The Annals of Mathematical Statistics 30, no. 1 (1959): 165–68. [http://www.jstor.org/stable/2237130](http://www.jstor.org/stable/2237130).

[Scarf, 1967] Scarf, Herbert E. “The Core of an N Person Game.” Econometrica 35, no. 1 (1967): 50–69. [https://doi.org/10.2307/1909383](https://doi.org/10.2307/1909383).

[DPSV, 2002] N. R. Devanur, C. H. Papadimitriou, A. Saberi and V. V. Vazirani, "Market equilibrium via a primal-dual-type algorithm," The 43rd Annual IEEE Symposium on Foundations of Computer Science, 2002. Proceedings., Vancouver, BC, Canada, 2002, pp. 389-395, doi: [10.1109/SFCS.2002.1181963](https://doi.org/10.1109/SFCS.2002.1181963). 

[LMMS, 2004] R. J. Lipton, E. Markakis, E. Mossel, and A. Saberi. 2004. On approximately fair allocations of indivisible goods. In Proceedings of the 5th ACM conference on Electronic commerce (EC '04). Association for Computing Machinery, New York, NY, USA, 125–131. [https://doi.org/10.1145/988772.988792](https://doi.org/10.1145/988772.988792).

[AG, 2004] Ageev, A.A., & Sviridenko, M. (2004). Pipage Rounding: A New Method of Constructing Algorithms with Proven Performance Guarantee. Journal of Combinatorial Optimization, 8, 307-328.

[RTV, 2011] Nisan, Noam, Tim Roughgarden, Eva Tardos, and Vijay V. Vazirani, eds. Algorithmic Game Theory. Cambridge: Cambridge University Press, 2007.

[DS, 2014] Darmann, Andreas and Schauer, Joachim, Maximizing Nash Product Social Welfare in Allocating Indivisible Goods (March 15, 2014). Available at SSRN: [http://dx.doi.org/10.2139/ssrn.2410766](http://dx.doi.org/10.2139/ssrn.2410766).

[CG, 2015] Richard Cole and Vasilis Gkatzelis. 2015. Approximating the Nash Social Welfare with Indivisible Items. In Proceedings of the forty-seventh annual ACM symposium on Theory of Computing (STOC '15). Association for Computing Machinery, New York, NY, USA, 371–380. [https://doi.org/10.1145/2746539.2746589](https://doi.org/10.1145/2746539.2746589)

[Lee, 2015] Euiwoong Lee, APX-hardness of maximizing Nash social welfare with indivisible items, Information Processing Letters, Volume 122, 2017, Pages 17-20, ISSN 0020-0190, [https://doi.org/10.1016/j.ipl.2017.01.012](https://doi.org/10.1016/j.ipl.2017.01.012).

[AGSS, 2016] Anari, N., Gharan, S.O., Saberi, A., & Singh, M. (2016). Nash Social Welfare, Matrix Permanent, and Stable Polynomials. ArXiv, abs/1609.07056.

[Procaccia, 2016] Procaccia, A. D. (2016). Cake Cutting Algorithms. In F. Brandt, V. Conitzer, U. Endriss, J. Lang, & A. D. Procaccia (Eds.), Handbook of Computational Social Choice (pp. 311–330). chapter, Cambridge: Cambridge University Press.
 
[CDGJMVY, 2017] Richard Cole, Nikhil Devanur, Vasilis Gkatzelis, Kamal Jain, Tung Mai, Vijay V. Vazirani, and Sadra Yazdanbod. 2017. Convex Program Duality, Fisher Markets, and Nash Social Welfare. In Proceedings of the 2017 ACM Conference on Economics and Computation (EC '17). Association for Computing Machinery, New York, NY, USA, 459–460. [https://doi.org/10.1145/3033274.3085109](https://doi.org/10.1145/3033274.3085109)

[BKV, 2018] Siddharth Barman, Sanath Kumar Krishnamurthy, and Rohit Vaish. 2018. Finding Fair and Efficient Allocations. In Proceedings of the 2018 ACM Conference on Economics and Computation (EC '18). Association for Computing Machinery, New York, NY, USA, 557–574. [https://doi.org/10.1145/3219166.3219176](https://doi.org/10.1145/3219166.3219176).

[CKMPSW, 2019] Ioannis Caragiannis, David Kurokawa, Hervé Moulin, Ariel D. Procaccia, Nisarg Shah, and Junxing Wang. 2019. The Unreasonable Fairness of Maximum Nash Welfare. ACM Trans. Econ. Comput. 7, 3, Article 12 (August 2019), 32 pages. [https://doi.org/10.1145/3355902](https://doi.org/10.1145/3355902).
 
[LV, 2021] W. Li and J. Vondrák, "A constant-factor approximation algorithm for Nash Social Welfare with submodular valuations," 2021 IEEE 62nd Annual Symposium on Foundations of Computer Science (FOCS), Denver, CO, USA, 2022, pp. 25-36, doi: [10.1109/FOCS52979.2021.00012](https://doi.org/10.1109/FOCS52979.2021.00012).

[ABFV, 2022] Amanatidis, G., Birmpas, G., Filos-Ratsikas, A., & Voudouris, A.A. (2022). Fair Division of Indivisible Goods: A Survey. ArXiv, abs/2208.08782.

 [GHLVV, 2023] Jugal Garg, Edin Husić, Wenzheng Li, László A. Végh, and Jan Vondrák. 2023. Approximating Nash Social Welfare by Matching and Local Search. In Proceedings of the 55th Annual ACM Symposium on Theory of Computing (STOC 2023). Association for Computing Machinery, New York, NY, USA, 1298–1310. [https://doi.org/10.1145/3564246.3585255](https://doi.org/10.1145/3564246.3585255)
 
 [BLPS, 2024] Brown, Adam, Aditi Laddha, Madhusudhan Reddy Pittu, and Mohit Singh. ‘Approximation Algorithms for the Weighted Nash Social Welfare via Convex and Non-Convex Programs’. In Proceedings of the 2024 Annual ACM-SIAM Symposium on Discrete Algorithms (SODA), 1307–27, n.d. [https://doi.org/10.1137/1.9781611977912.52](https://doi.org/10.1137/1.9781611977912.52).

[FL, 2024] Yuda Feng and Shi Li. A Note on Approximating Weighted Nash Social Welfare with Additive Valuations. In 51st International Colloquium on Automata, Languages, and Programming (ICALP 2024). Leibniz International Proceedings in Informatics (LIPIcs), Volume 297, pp. 63:1-63:9, Schloss Dagstuhl – Leibniz-Zentrum für Informatik (2024) [https://doi.org/10.4230/LIPIcs.ICALP.2024.63](https://doi.org/10.4230/LIPIcs.ICALP.2024.63)
 
[FHLR, 2024] Yuda Feng, Yang Hu, Shi Li, & Ruilong Zhang. (2024). Constant Approximation for Weighted Nash Social Welfare with Submodular Valuations. 

