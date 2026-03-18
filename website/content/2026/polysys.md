+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "Polysys: an Algebraic Leakage Attack Engine "
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2026-03-17

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Security"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
# Consider these similar to keywords specified for a research paper
tags = ["Encrypted Search", "Security", "Applied Cryptography"]

[extra]
author = {name = "Andrew Park", url = "https://andyp223.github.io/"}
# The committee specification is a list of objects similar to the author.
committee = [
    {name = "William Kuszmaul", url = "https://sites.google.com/site/williamkuszmaul"},
    {name = "Aayush Jain", url = "https://sites.google.com/view/aayushjain/home"},
    {name = "Mingkuan Xu", url = "https://mingkuan.taichi.graphics/"}
]
+++

# Introduction 

Consider a scenario in which a hospital wishes to store their highly sensitive data on a third-party database server (such as AWS). Because they are afraid of scenarios such as data breaches or regulatory audits, the hospital will often store the data encrypted using a primitive such as AES. However, while encryption addresses the problem of security at rest (i.e. when the data is not used), the hospital wil still need to unencrypt the data in order to perform expressive database queries on the data since standard encryption does not support query functionality. This causes a huge problem: at the moment of decryption on the server, that instance provides an opportunity for malicious attacks, allowing access to the sensitive data in plaintext. Indeed, such [data breaches](https://www.hipaajournal.com/aflac-data-breach/) are still common due to this tension between security and functionality that arises when using standard encryption. 

To address this problem, cryptographers are researching a suite of techniques called encrypted search algorithm (ESAs), which provide a best of both worlds solution to the above issue. ESAs are cryptographic algorithms that allow a client to perform searches over encrypted documents, meaning that the data will never have to be decrypted on the server. When designing these algorithms, the three main things to consider are: 

* correctness: the algorithm should maintain the same corectness guarantees as a plaintext search algorithm 
* performance: the schemes should be fast, ideally as close as possible to the plaintext version. Theoretically, this means the scheme should run in time sublinear in the number of records stored in the server
* security: at a high level, the scheme should mathematically guarantee that an attacker is able to learn nothing about the secret queries or secret data at the server.  

It is well known, however, that achieving all three properties at the same time is impossible. In particular, in order to achieve sub-linear search time in the number of documents, ESAs must leak some information about the queries and/or data. This leakage (also called metadata leakage) is formally captured by a leakage profile, which describes what the scheme precisely reveals. One common leakage profile is the (range)-response identity (RID), which leaks which documents (or keys) were returned for each (range) query. We illustrate an example in the figure below: 


<table>
  <tr>
    <td style="width:50%; text-align:center; vertical-align:top;">
      <img src="rid1.png" width="100%"><br>
      <em>Example of a sequence of range queries performed on a small database. Here, the queries are secret to the attacker.</em>
    </td>
    <td style="width:50%; text-align:center; vertical-align:top;">
      <img src="rid2.png" width="100%"><br>
      <em>What the adversary sees under the range response identity leakage profile. The adversary is only able to see which documents were returned for each query, but is not able to see the query sequence nor the contents of the database entries themselves.</em>
    </td>
  </tr>
</table>


<!-- | | |
|:-:|:-:|
| ![Example of a equence of queries on small database of 5 records.](rid1.png) | ![What the adversary sees under the range response identity leakage profile](rid2.png) |
| **(a)** Example of a sequence of range queries performed on a small database. Here, the queries are secret to the attacker. | **(b)** What the adversary sees under the range response identity leakage profile. The adversary is only able to see which documents were returned for each query, but is not able to see the query sequence nor the contents of the database entries themselves.| -->

An extensive line of work on leakage attacks has designed various cryptanalytic techniques to exploit different leakage profiles in order to recover as much information about the underlying secret information as possible. These attacks can be largely categorized into three main groups: 

* inference atacks, which take in as input a leakage pattern and some auxiliary information about the queries/data (e.g. their distributions), and output a recovered query sequence/ dataset 
* resolution attacks, which take in as input leakage pattern and outputs a recovered query sequence / dataset. Note that the attack in this case does not take in any information beyond the leaked pattern.
* known-data attacks, which take in as input a leakage pattern and some fraction of known data, and output the recovered query sequence/ data. 

The current landscape of leakage attacks, however, is highly fragmented, with most attacks designed in an ad hoc, scheme-specific manner rather than derived from a unifying methodology. This means that for every construction, a new attack must be tailored to its particular leakage profile, data model, or assumptions specific to that scheme. In practice, this means that two attacks cannot be easily compared to each other. This fragmentation makes it challenging to reason formally about attack optimality or completeness, and slows progress by requiring cryptographers to repeatedly rediscover similar inference strategies in slightly different forms.

The table below shows some of the prior inference and known-data attacks for the (range)-response identity pattern along with the leakage pattern and auxiliary information scenario they consider in their work. Note that each of the six attacks below all make different assumptions about the query sequence and data distribution even though they are all considering the same leakage profiles. 

| Attack     | Target                | Leakage Profile       | Query Assumptions? | Data Assumptions? | 
|:---------- | :---------------------|:---------------------|:---------------------|:---------------------|
| Count  | K        | rid | Non-repeating| N/A | 
| Subgraph-ID       | K | rid            | Non-repeating | N/A | 
| LMP-ID |   RV               | (range)-rid               | N/A | Dense |
| LMP-APP |   RV             | (range)-rid                  |   N/A| Dense |
| GenKKNO |  RV             | (range)-rid                  |  Uniform | N/A|
| ApproxValue |   RV            | (range)-rid                  | Uniform | Specific|  

To this end, we design Polysys (short for Polynomial System), a novel framework for modeling and designing leakage attacks as polynomials constraints. Below, we describe how to formalize the system of equations and then demonstrate how to use a SAT solvers to solve these equations efficiently. We then compare Polysys' recovery rates to prior state of the art attacks and demonstrate that our generalized approach is comparable to the recovery rates exhibited by prior works. 

# Preliminaries

We model the document search problem as follows. We treat the database as a collection of key/tuple pairs where the set of possible keys is \\([1,N]\\), where \\(N\\) is the domain size, and the tuple is the list of documents that contain that key. More formally, we treat the multi-map \\(MM\\)as a collection of label/tuple pairs \\({(l_i, v_{i,j}), i \in [N], j \in |MM[l_i]|}\\). We use \\(r\\) to represent the number of documents. The goal of a leakage attack is therefore: given a sequence of \\(t\\) queries \\(q_1,...,q_t\\), recover the unknown queries and key/tuple pairs.

We focus on two different types of search: point or key search and range search, which support different types of queries. Point search supports equality queries, which means that the queries take the form \\(q = j \in \[1,N\]\\). This captures settings in which the database supports queries such as, "which documents contain the word 'apple'"? Range queries take the form \\(q_i = \[l,r\], l,r \in \[1,N\], l \leq r\\). For range queries, we additionally impose the assumption that each document only contains a single value. This assumption was used in all prior range query attacks, and captures the fact that most data columns which support range queries (i.e. age, income) often contain a single numerical value.

<!-- # Leakage Patterns

<!--
## Query Equality Pattern 

Given a sequence of queries \\(q_1,...,q_t\\), the query equality pattern leaks whether two queries are identical or different. This is captured by the \\(t\\) by \\(t\\) matrix \\(L\\) 

where $$L_{i,j} = 
\begin{cases}
    1 & \textnormal{if\ } q_i = q_j,\\\\
    0 & \textnormal{otherwise}. 
\end{cases}
$$
-->

<!-- ## Response Identity Pattern 

Given a sequence of queries \\(q_1,...,q_t\\) and a multi-map \\(MM\\), the response identity of a query sequence is defined as 

\\(rid(MM, q_1,...,q_t) = I\\) where 

$$I_{i,j} = 
\begin{cases}
    1 & \textnormal{if\ } v_j \in MM[q_i],\\\\
    0 & \textnormal{otherwise}. 
\end{cases}
$$

In the case of range queries, the above definition is generalized naturally where 

$$I_{i,j} = 
\begin{cases}
    1 & \textnormal{if\ } \bigcup MM[l], l \in q_i,\\\\
    0 & \textnormal{otherwise}. 
\end{cases}
$$ --> 

# The Polynomial Constraint Framework 

Our first insight comes from translating the leakage attack problem into an algebraic system of equations. Solving this system of equations would then provide a candidate secret that would output the observed leakage. To do this, we first represent the query sequence and secret data as matrices \\(Q,D\\) respectively. We then show how to represent these matrices using a system of constraints (called structure constraints). At a high level, these constraints capture the structure of what the secret information must look like, independent of the leakage pattern. 

## Structure Constraints 

Structure equations encode the inherent invariants of the underlying encrypted data system, independent of any particular leakage instance. At a high level, consider the case in which we wish \\(Q\\) to represent a sequence of \\(t\\) range queries. What properties would \\(Q\\) need to satisfy? Similarly, we would need \\(D\\) to follow certain invariants in order for \\(D\\) to represent a valid data matrix.

As an example, one way we could model \\(Q\\) for a sequence of queries \\(q_1,...,q_t\\) is as a \\(t\\) by \\(N\\) binary matrix \\(Q\\) where 

$$Q_{i,j} = 
\begin{cases}
    1 & \textnormal{if\ } j \in q_i,\\\\
    0 & \textnormal{otherwise}. 
\end{cases}
$$

Here, each row of the matrix represents a query, and the column represent whether that key was part of that query. 

## Leakage Constraints 

Leakage equations encode the information revealed through from the leakage profile. Each leakage profile translates into algebraic constraints that restrict the possible values of the hidden variables. Unlike structure equations, which hold regardless of the leakage profile, leakage equations are instance-specific and reflect the adversary’s view of a particular execution. Together with the structure equations, they shrink the feasible solution space until the solver can recover assignments that are both structurally valid and consistent with the observed leakage.

<!--
In the case of point queries, this means that by definition, each row of \\(Q\\) can only have a single \\(1\\) in every row. This can be captured by the following \\(O(t)\\) constraints: 

$$\sum_{j = 1}^N Q_{i,j} = 1, \ i \in [t]$$

In the case of range queries, the sequence of \\(1\\)'s must in each row must be consecutive. This can be captured by the following \\(O(t)\\) constraints: 

$$ \sum_{j = 1}^{N - 1} Q_{i,j} \cdot Q_{i,j+1} = \sum_{j = 1}^N Q_{i,j} + 1,\ i \in [t]$$ 

By themselves, note that these constraints do not tell us anything about the secret query sequence. All that is says is that a valid query sequence must satisfy these constraints. 

### Encoding Multi-maps 

Given a multi-map \\(MM\\) that contains \\(r\\) documents with keywords over a domain size \\(N\\), we are also able to structure this information as a \\(N\\) by \\(r\\) binary matrix \\(D\\), where: 

$$D_{i,j} = 
\begin{cases}
    1 & \textnormal{if document \ } j \textnormal{\ contains keyword \ } i,\\\\
    0 & \textnormal{otherwise}. 
\end{cases}
$$

Each row of this matrix represents the which of the \\(r\\) documents contains keyword \\(i\\) and each column represents which keywords are contained for that specific document. Note that in the case of point multi-maps, there are no restrictions on what keywords are contained in each document, meaning no additional constraints are required - however, in the case of range multi-maps, we impose the constraint that each document only contains a singular keyword. This can be written in the following $O(r)$ constraints, one for each column: 

$$\sum_{j = 1}^N D_{i,j} = 1, \ j \in [r]$$ -->

<!-- ## Leakage Constraints 

Apart from capturing the structure constraints, we now show how to derive the leakage polynomial systems for two of the most common leakage patterns in the leakage attack literature: query equality (qeq) and response identity (rid). By combining the leakage constraints with the syntax constraints above, this gives us a complete system that allows us to solve for the secret in both the point and range query settings.  -->

<!-- ### QEQ Constraints 
Based on our query sequence encoding above for queries \\(q_1,\cdots,q_t\\), observe that \\(Q \cdot Q^T = E\\)

where $$E_{i,j} = 
\begin{cases}
    1 & \textnormal{if\ } q_i = q_j,\\\\
    0 & \textnormal{otherwise}. 
\end{cases}
$$

At a high level, \\(E_{i,j}\\) represents the dot product between two one-hot vectors with the non-zero index at \\(q_i\\) and \\(q_j\\) respectively. The dot product thus equals \\(1\\) iff \\(q_i = q_j\\). 

Equivalently, we can think of the qeq equations as the following \\(O(t^2)\\) equations: 

$$\sum_{k=1}^t Q_{i,k} \cdot Q_{j,k} = E_{i,j}, i,j \in [t], i < j$$ -->

<!-- ### RID Constraints

Based on our matrix representations of \\(Q\\) and \\(D\\) above, we have that \\(Q \cdot D = L\\) 
where \\(L = rid(MM, q_1,...,q_t)\\). From here, we are able
 to rewrite this as \\(O(t\cdot N)\\) linear equations: 

$$ \sum_{k = 1}^t Q_{i,k} \cdot D_{k,j} = L_{i,j}, \ i \in [t], j \in [N]$$ -->

## Combining the Constraints Together

Combining the above polynomial equations gives us a system that can theoretically be solved for a candidate solution for a given leakage profile. As an example, we write the full system below for RID for range queries (recall that \\(Q,D\\) are the secret data we are trying to reconstruct, and L is publicly leaked by the scheme we are attacking):

1. \\( \sum_{j = 1}^{N - 1} Q_{i,j} \cdot Q_{i,j+1} = \sum_{j = 1}^N Q_{i,j} + 1,\ i \in [t]\\) 
1. \\(\sum_{j = 1}^N D_{i,j} = 1, \ j \in [r]\\)
1. \\(\sum_{k = 1}^t Q_{i,k} \cdot D_{k,j} = L_{i,j}, \ i \in [t], j \in [N]\\)

Above, Constraint \\(1\\) tells us that the queries are range queries. Constraint \\(2\\) tells us that every document can only contain exactly one keyword (which is our assumption for range query schemes). Finally, the last set of constraints is used when atacking the RID leakage pattern. Finding a solution to these set of polynomial equations gives us a candidate \\(Q,D\\) which represents a possible secret that outputted the observed leakage pattern. Note that if there are several possible solutions, then the attacker would not know which is the correct one so they can only choose one candidate arbitrarily. 

# From Polynomials to SAT 

While the above set of polynomial equations are theoretically solveable using known algebraic methods, the second main challenge in designing an efficient attack engine comes from developing a technique that allows the adversary to solve these constraints efficiently. To address this challenge, we turn to SAT solvers, which are programs explicitly designed to heuristically find a satisfying instance to a constraint problem if one exists, or to output unsatisfiable otherwise. Note that the boolean satisfiability problem is theoretically NP-hard, so this method is only a heuristic based approach to solve these programs quickly in practice. 

Our main observation is that by utilizing SAT solving techniques to reduce the polynomial constraints into an equivalent CNF, we can use a SAT solver in order to efficiently find a satisfying instance to the polynomial constraint system. This represents a possible query/data solution to the observed leakage pattern.

The main challenge in this step, therefore, is to find a way to do the polynomial-to-SAT translation efficiently. To see why this is difficult, consider the linear equation \\(\sum_{i=1}^\gamma x_i = 1\\) (an example of one of the polynomial constraints seen in Polysys). A naive approach of translating this to a SAT-friendly formulation could be: 

\\(
  \bigg(\bigvee_{i\in [\gamma]} x_i \bigg)
  \wedge
  \bigg(
  \bigwedge_{i \neq j}  \overline{x}_i \vee \overline{x}_j
  \bigg)
\\)

where the first set of terms captures that at least one variable is equal to 1 while the second term captures the fact that two variables cannot be true at the same time. Although this representation is theoretically equivalent, it requires at least \\(O(\gamma^2)\\) clauses which is prohibitive in practice. Therefore, the SAT translation step requires design new techniques that would allow for efficient translation of these constraints in the context of Polysys. For example, we are able to obtain a translation that requires only  \\(O(\gamma)\\) clauses, which is optimal (see our paper for details)! 

Ultimately, by rewriting all of the polynomial constraints appropriately, we obtain a set of CNF constraints that can be solved by a SAT solver efficiently. This satisfying assignment can then be directly mapped back to a recovered secret. 

In summary, combining the techniques from the above two sections gives us a conjunction of CNFs corresponding to the original system of polynomial equations. Intuitively, if the number of satisfying assignments is small, this means that the original system of equations (and thus leakage pattern) is easy to attack. Similarly, if the number of assignments is large, then the original system of equations is difficult to attack. 

<!--
We illustrate two of the techniques we use to do this below. 

## Binary Sum to One (Constraint 2)

If we wished to write the linear equation \\(\sum_{i=1}^\gamma x_i = 1\\) (such as the ones in Constraint 2) as a CNF formulation, a naive approach could be the following: 
\\(
   \bigg(\bigvee_{i\in [\gamma]} x_i \bigg)
   \wedge
   \bigg(
   \bigwedge_{i \neq j}  \overline{x}_i \vee \overline{x}_j
   \bigg)
\\)

where the first set of terms captures that at least one variable is equal to 1 while the second term captures the fact that two variables cannot be true at the same time. While this representation is equivalent to the linear equation above, it requires at least \\(O(\gamma^2)\\) clauses which is prohibitive in practice. 

An alternative, more efficient approach is as follows. Define \\(ND(x_1,...,x_i)\\) to be the naive approach described above. Then we are able to recursive define the function \\(AMO(x_1,...,x_\gamma)\\) as follows: 

$$ AMO(x_1,...,x_\gamma) = ND(x_1,x_2,x_3,y) \vee AMO(\overline{y},x_4,...,x_\gamma)$$ 

Here, \\(y\\) is called the commander variable which "controls" where the single true is located. If located among the first three \\(x_i\\)'s, then \\(y\\) would be equal to 0. Alternatively, if there are no trues among the first three variables, then \\(y\\) would equal true, guaranteeing that the single true is located among the remaining \\(x_i\\)'s. Note that the naive enumeration of the first term requires only \\(P(1)\\) clauses. This means that this alternative approach only requires \\(O(N)\\) clauses at the cost of \\(O(N)\\) additional variables. This tradeoff is favorable to the SAT solver in practice. 

## Continguous Ones for Range Queries (Constraint 1)

Another type of equation we must rewrite are range query structure constraints, which capture the fact that all of the one's must be continguous within the range. A naive way to represent this is to fully enumerate all of the n choose 2 possibilities, which is clearly expensive. Our observation is that we can transform this into an equivalent representation that only requires \\(O(\gamma)\\) clauses by using \\(O(\gamma)\\)additional variables as follows. 

We first introduce the variables \\(a_1, \dots, a_\gamma\\) and \\(b_1, \dots, b_\gamma\\) where \\(a_i = 1\\) if there exists \\(j\geq i\\)  such that \\(x_j = 1\\) and \\(b_i = 1\\) if there exists \\(j \leq i\\) such that \\(x_j = 1\\). These definitions are captured by the following constraints:

$$x_i\implies a_i  \equiv\overline{x_i} \vee a_i$$ 
$$a_{i+1} \implies a_i \equiv \overline{a_{i+1}} \vee a_i$$
$$x_i\implies b_i \equiv \overline{x_i} \vee b_i$$ 
$$ b_{i} \implies b_{i+1} \equiv \overline{b_{i}} \vee b_{i+1} $$

We finally ensure that there is no index \\(i \in [\gamma]\\) such that \\(x_i = 1\\) and \\(a_i =1\\) and \\(b_i = 1\\). We capture this by,
$$ x_i \vee \overline{a_i} \vee \overline{b_i}, \quad i \in [\gamma]. $$
The final Boolean expression is the conjunction of all these clauses. 
-->

# Evaluation 

We implement the PolySys engine described above in Python and compare performance against prior state-of-the-art attacks on various real-world and synthetic workloads. We highlight some of the results here when comparing against state of the art prior attacks. Note that in each section, we are comparing Polysys against the state of art attacks that were designed to attack that specific leakage profile under specific assumptions. We explain further below. 

## Known data attacks against rid 

Figures a and b below show the recovery rates of Polysys, Count, and Subgraph attacks when varying the known data rate on the Enron dataset. The Enron dataset is a standard dataset used when evaluated query attacks for different leakage patterns. We consider two cases where user queries are sampled uniformly or following a Zipf distribution. The query sequence length was set to 150, and the recovery rate is computed as the fraction of queries (out of 150) that are correctly matched. 

| | |
|:-:|:-:|
| ![Attack on Enron dataset using Uniform Queries](figure_1a.png) | ![Attack on Enron dataset using Zipf Queries](figure_1b.png) |
| **(a)** Uniform | **(b)** Zipf(\\(\alpha=2\\)) |

Here, Polysys outperforms both other attacks in low and high known data rates. Even with a 10% known data rate, Polysys achieves a recovery rate of 92% and 79% with uniform and Zipf-distributed queries respectively, whereas Subgraph has a low recovery rate of 9% and 1%. This nontrivial gap is probably because Polysys does exceptionally well in extracting all the information from the leakage as it fully describes it as a system of equations. We note that the recovery rate of Polysys (and all other attacks) dropped when the query distribution was changed from uniform to Zipf since less unique queries are seen with more skewed distributions.

## Data recovery attacks against range-rid 

Figures a and b below show the recovery rate of the GenKKNO, ApproxValue, LMP, and Polysys on the MIMIC dataset for uniform and Zipf-distributed queries, respectively. The MIMIC dataset is a health data consisting of various medical metrics.  The recovery rate is the mean absolute error between the actual and the recovered dataset. As expected, Polysys slightly underperforms prior work in the uniform case while outperforming them in the Zipf case as the number of queries increases. The slight underperformance in the uniform case is due to hardcoded distributional knowledge in the attacks; an assumption Polysys does not use. Specifically, GenKKNO and ApproxValue were explicitly designed for the uniform query case. This explains the difference in performance between the uniform and Zipf case.

| | |
|:-:|:-:|
| ![Attack on MIMIC dataset using Uniform Queries](figure_3a.png) | ![Attack on MIMIC dataset using Zipf Queries](figure_3b.png) |
| **(a)** MIMIC, Uniform | **(b)** MIMIC, Zipf(\\(\alpha=2\\)) |
| ![Attack on synthetic dense dataset using Uniform Queries](figure_3c.png) | ![Attack on synthetic dense dataset using Zipf Queries](figure_3d.png) |
| **(c)** MIMIC, Uniform | **(d)** Dense, Zipf(\\(\alpha=2\\)) |

Because LMP and LMP-APP are only usable in the case where the dataset is dense (e.g., there exists at least one record for each value in the domain), we additionally test Polysys and the other attacks on a synthetic dense dataset for the same size as the MIMIC dataset. We do this by fixing N records/values to be each value in the domain \\(N\\) and then uniformly sampling the remainder. The results of the attacks for uniform and Zipf-distributed query sequences on this synthetic dataset are shown in Figures c and d above. In the dense case, Polysys again outperforms all prior work. In particular, Polysys can obtain \\(>\\)99% data reconstruction and \\(>\\)85% reconstruction rate in the uniform and Zipf case, respectively, with 300 queries.
Similar to the point attacks, varying the query distribution and, in this case, the data distribution can impact the recovery rate. 

# Limitations and Conclusion  

Although Polysys works well for a small number of constraints,  its scalability is limited due to the number of variables and CNF constraints required to represent the observed leakage. Future work can look at more efficient ways in compiling the polynomial constraints to CNF as well as looking to generalize Polysys further to capture more complicated leakage patterns. 

While we were not able to discuss all of our techniques and results here, we refer the reader to our USENIX paper [here](https://eprint.iacr.org/2025/1530) to see a more complete view of our contributions. 