+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "The NeurIPS 2024 Paper-Reviewer Assignment Algorithm"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2025-06-05

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Artificial Intelligence"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
# Consider these similar to keywords specified for a research paper.
tags = ["peer-review"]

[extra]
author = {name = "Yixuan Xu", url = "https://yixuanevenxu.github.io/" }
# The committee specification is  a list of objects similar to the author.
committee = [
    {name = "Vincent Conitzer", url = "https://www.cs.cmu.edu/~conitzer/"},
    {name = "Nihar B. Shah", url = "https://www.cs.cmu.edu/~nihars/"},
    {name = "Runtian Zhai", url = "https://www.runtianzhai.com/"}
]
katex_enable = true
katex_auto_render = true
+++


# Overview

Paper assignment is crucial in conference peer review as we need to ensure that papers receive high-quality reviews and reviewers are assigned papers that they are willing and able to review. Moreover, it is essential that a paper-matching process mitigates potential malicious behavior, e.g., authors and reviewers forming collusion rings to get favorable reviews. The default paper assignment approach used in previous years of NeurIPS is to find a deterministic maximum-quality assignment using linear programming. This year, for NeurIPS 2024, as a collaborative effort with the organizing committee, we experimented with a new assignment algorithm [1] that introduces randomness to improve robustness against potential malicious behavior, as well as enhance reviewer diversity and anonymity, while maintaining most of the assignment quality. In the rest of this post, we introduce the details of the algorithm, explain how we implemented it, and analyze the deployed assignment for NeurIPS 2024. This post was originally published on the NeurIPS 2024 [conference blog website](https://blog.neurips.cc/2024/12/12/neurips-2024-experiment-on-improving-the-paper-reviewer-assignment/).

<!-- Optional: Inline style or other customizations here -->

<script>
document.addEventListener("DOMContentLoaded", function() {
  // Re-run auto-render with custom delimiters
  renderMathInElement(document.body, {
    delimiters: [
      {left: '$$', right: '$$', display: true},
      {left: '$', right: '$', display: false}
    ],
    throwOnError: false
  });
});
</script>

# The Algorithm

The assignment algorithm we used is Perturbed Maximization (PM) [[1]](https://arxiv.org/pdf/2310.05995), a work published at NeurIPS 2023. To introduce the algorithm, we first briefly review the problem setting of paper assignment in peer review as well as the default algorithm used in previous years.

## Problem Setting and Default Algorithm

In a standard paper assignment setting, a set $\mathcal{P}$ of $n^{(p)}$ papers needs to be assigned to a set $\mathcal{R}$ of $n^{(r)}$ reviewers. To ensure each paper receives enough reviewers and no reviewer is overloaded with papers, each paper $p$ in $\mathcal{P}$ should be assigned to $\ell_p$ reviewers and each reviewer $r$ in $\mathcal{R}$ should receive no more than $\ell_r$ papers. An assignment is represented as a binary matrix $\mathbf{x}$ in $\lbrace 0,1\rbrace^{n^{(p)} \times n^{(r)}}$, where $x_{p,r} = 1$ indicates that paper $p$ is assigned to reviewer $r$. The main objective of paper assignment is usually to maximize the predicted match quality between reviewers and papers [2]. To characterize the matching quality, a similarity matrix $\mathbf{S}$ in $\mathbb{R}^{n^{(p)} \times n^{(r)}}$ is commonly used [2-8]. Here, $S_{p,r}$ represents the predicted quality of a review by reviewer $r$ for paper $p$ and is generally computed from various sources [9], e.g., reviewer-selected bids representing their personal preferences about the papers and affinity scores between the paper and the reviewer's past work computed by natural language processing methods [2, 10-13]. For any conflicts, the similarity scores will be set to $-\infty$. Then, the **quality** of an assignment can be defined as the total similarity of all assigned paper-reviewer pairs, i.e., $\mathrm{Quality}(\mathbf{x}) = \sum_{p,r} x_{p,r} S_{p,r}.$ One standard approach for computing a paper assignment is to maximize quality [2, 5-8, 14], i.e., to solve the following optimization problem:

<div style="white-space: pre-wrap;">
$$
\begin{array}{lll}
	\textup{Maximize} & \mathrm{Quality}(\mathbf x) \stackrel{\text{def}}{=} \sum_{p,r}x_{p,r}S_{p,r} \\
	\textup{Subject to} & \sum_r x_{p,r}=\ell_p &\forall p\in\mathcal P,\\
		& \sum_p x_{p,r}\leq \ell_r &\forall r\in\mathcal R,\\
		& x_{p,r}\in \lbrace 0, 1\rbrace & \forall p\in\mathcal P,r\in\mathcal R.
\end{array}
$$
</div>

The optimization above can be solved efficiently by linear programming and is widely used in practice. In fact, the default automatic assignment algorithm used in OpenReview is also based on this linear programming formulation and has been used in NeurIPS in past years.

## Perturbed Maximization

While the deterministic maximum-quality assignment is the most common, there are strong reasons [1, 17] to introduce randomness into paper assignment, i.e., to determine a probability distribution over feasible deterministic assignments and sample one assignment from the distribution. For example, one important reason is that randomization can help mitigate potential malicious behavior in the paper assignment process. Several computer science conferences have uncovered "collusion rings" of reviewers and authors [15-16], in which reviewers aim to get assigned to the authors' papers in order to give them good reviews without considering their merits. Randomization can help break such collusion rings by making it harder for the colluding reviewers to get assigned to the papers they want. The randomness will also naturally increase reviewer diversity and enhance reviewer anonymity.

Perturbed Maximization (PM) [1] is a simple and effective algorithm that introduces randomness into paper assignment. Mathematically, PM solves a perturbed version of the optimization problem above, parameterized by a number $Q \in [0, 1]$ and a "perturbation function" $f : [0, 1] \to [0, 1]$:

<div style="white-space: pre-wrap;">
$$
\begin{array}{lll}
	\textup{Maximize} & \mathrm{PQuality}(\mathbf x) \stackrel{\text{def}}{=} \sum_{p,r}f(x_{p,r})S_{p,r} \\
	\textup{Subject to} & \sum_r x_{p,r}=\ell_p &\forall p\in\mathcal P,\\
		& \sum_p x_{p,r}\leq \ell_r &\forall r\in\mathcal R,\\
		& x_{p,r}\in [0, Q] & \forall p\in\mathcal P,r\in\mathcal R.
\end{array}
$$
</div>

In this perturbed optimization, the variables $x_{p,r}$ are no longer binary but continuous in $[0, Q]$. This is because we changed the meaning of $x_{p,r}$ in the randomized assignment context: $x_{p,r}$ now represents the marginal probability that paper $p$ is assigned to reviewer $r$. By constraining $x_{p,r}$ to be in $[0, Q]$, we ensure that each paper-reviewer pair has a probability of at most $Q$ to be assigned to each other. This constraint is adopted from an earlier work on randomized paper assignment [17]. The perturbation function $f$ is a concave function that is used to penalize high values of $x_{p,r}$, so that the probability mass is spread more evenly among the paper-reviewer pairs. The perturbation function can be chosen in various ways, and one simple option is $f(x) = x - \alpha x^2$ for some $\alpha > 0$, which makes the optimization concave and quadratic, allowing us to solve it efficiently.

After solving the optimization problem above, we obtain a probabilistic assignment matrix $\mathbf{x} \in [0, Q]^{n^{(p)} \times n^{(r)}}$. To get the final assignment, we then sample according to the method in [17-18] to meet the marginal probabilities $\mathbf{x}$. The method is based on the Birkhoff-von Neumann theorem.

# Implementation

Since this is the first time we use a randomized algorithm for paper assignment at NeurIPS, the organizing committee decided to set the parameters so that the produced assignment is close in quality to the maximum-quality assignment, while introducing a moderate amount of randomness. Moreover, we introduced additional constraints to ensure that the randomization does not result in many low-quality assignments.

## Similarity Computation of NeurIPS 2024

The similarity matrix $\mathbf{S}$ of NeurIPS 2024 was computed from two sources: affinity scores between the paper and the reviewer's past work and bids submitted by reviewers representing their preferences. The affinity scores were computed using a text similarity model comparing the paper's text with the reviewer's past work on OpenReview. The resulting affinity scores were normalized to be within $[0, 1]$. The bids were collected from reviewers during the bidding phase, where reviewers could bid on papers they are interested in reviewing at five levels: "Very High", "High", "Neutral", "Low", and "Very Low". We mapped these bids to $(-1, -0.5, 0, 0.5, 1)$ respectively. The final similarity matrix was computed as the sum of the normalized affinity scores and the mapped bids, resulting in a similarity matrix consisting of numbers in $[-1, 2]$.

## Additional Constraints for Restricting Low-Quality Assignments

One of the main concerns of paper assignment in large conferences like NeurIPS is the occurrence of low-quality assignments because any individual low-quality paper-reviewer pair would lead to significant dissatisfaction of both the author and the reviewer. To mitigate this issue, we explicitly restrict the number of low-quality assignments. Specifically, we first solve another optimization problem without the perturbation function [17]:

<div style="white-space: pre-wrap;">
$$
\begin{array}{lll}
	\textup{Maximize} & \mathrm{Quality}(\mathbf x) \stackrel{\text{def}}{=} \sum_{p,r}x_{p,r} S_{p,r} \\
	\textup{Subject to} & \sum_r x_{p,r}=\ell_p &\forall p\in\mathcal P,\\
		& \sum_p x_{p,r}\leq \ell_r &\forall r\in\mathcal R,\\
		& x_{p,r}\in [0, Q] & \forall p\in\mathcal P,r\in\mathcal R.
\end{array}
$$
</div>

Let the optimal solution of this problem be $\mathbf{x}^{\ast}$. We want to ensure that adding the perturbation function does not introduce additional low-quality assignments compared to $\mathbf{x}^{\ast}$. To achieve this, we choose a set of thresholds $\tau \in \lbrace 0.1, 0.5, 1.0\rbrace$. For each $\tau$, we add constraints that our perturbed assignment should have at least the same number of assignments with quality above $\tau$ as $\mathbf{x}^{\ast}$, i.e.,

<div style="white-space: pre-wrap;">
$$
\begin{array}{lll}
	\textup{Maximize} & \mathrm{PQuality}(\mathbf x) \stackrel{\text{def}}{=} \sum_{p,r}f(x_{p,r})S_{p,r} \\
	\textup{Subject to} & \sum_r x_{p,r}=\ell_p &\forall p\in\mathcal P,\\
		& \sum_p x_{p,r}\leq \ell_r &\forall r\in\mathcal R,\\
		& x_{p,r}\in [0, Q] & \forall p\in\mathcal P,r\in\mathcal R,\\
		& \sum_{p,r} x_{p,r} \cdot \mathbb{I}\left[\vphantom{\sum}S_{p,r} \geq \tau\right] \geq \sum_{p,r} x^{\ast}_{p,r} \cdot \mathbb{I}\left[\vphantom{\sum}S_{p,r} \geq \tau\right] & \forall \tau \in \lbrace 0.1, 0.5, 1.0\rbrace.
\end{array}
$$
</div>

The thresholds $\lbrace 0.1, 0.5, 1.0\rbrace$ were chosen to distinguish between different levels of quality. According to the similarity computation for NeurIPS 2024, matchings with quality above $1.0$ are "good" ones that either the reviewer has a high affinity score with the paper and bids positively on it, or the reviewer bids "Very High" on the paper; matchings with quality above $0.5$ are "moderate" ones that either the reviewer has a high affinity score with the paper or the reviewer bids positively on it; matchings with quality above $0.1$ are "acceptable" ones that the reviewer has a moderate affinity score with the paper and bids neutrally on it. By setting these thresholds, we limited the number of low-quality assignments introduced by the perturbation function.

## Running the Algorithm

We integrated the Python implementation of PM into the [OpenReview system](https://github.com/openreview/openreview-matcher/pull/279), using Gurobi [19] as the solver for the concave optimization. However, since the number of papers and reviewers in NeurIPS 2024 is too large, we could not directly use OpenReview's computing resources to solve the assignment in early 2024. Instead, we ran the algorithm on a local server with anonymized data. The assignment was then uploaded to OpenReview for further processing, such as manual adjustments by the program committee. We ran four different parameter settings of PM and sampled three assignments from each setting. Each parameter setting took around 4 hours to run on a server with 112 cores, using peak memory of around 350GB. The final assignment was chosen by the program committee based on the computed statistics of the assignments. The final deployed assignment came from the parameter setting where $Q = 0.9$ and $f(x) = x - 0.1x^2$. The maximum number of papers each reviewer can review was set to $6$.


# Analysis of The Deployed Assignment

How did the assignment turn out? We analyzed various statistics of the assignment, including the aggregate scores, affinity scores, reviewer bids, reviewer load, and reviewer confidence in the review process. We also compared the statistics across different subject areas. Here are the results.

## Aggregate Scores

The deployed assignment achieved a mean aggregate score of $1.50$ and a median of $1.72$. Recall from the computation of the similarity matrix $\mathbf{S} \in [-1, 2]^{n^{(p)} \times n^{(r)}}$, this means the majority of the assignments are of very high quality, with high affinity scores and "Very High" bids. Additionally, we note that every single matched paper-reviewer pair has an aggregate score above $0.5$, which means that each assigned pair is at least a "moderate" match. In addition, we see no statistical difference in the aggregate score across different subject areas, despite the varying sizes of different areas.

![aggregate_scores](./aggregate_scores.png)

![papers_by_subject_area](./papers_by_subject_area.png)

![aggregate_scores_by_subject_area](./aggregate_scores_by_subject_area.png)


## Affinity Scores

Since the aggregate score is the sum of the affinity score based on text similarity and the converted reviewer bids, we also checked the distribution of these two key scores. The deployed assignment achieved high affinity scores, with a mean of $0.72$ and a median of $0.77$. Recall that the affinity scores are within $[0, 1]$. Note that there are also some matched pairs with zero affinity scores. These pairs are matched because the reviewers bid "Very High" on the papers, which results in an aggregate score of $1.0$. Therefore, we still prioritize these pairs over those with positive affinity scores but neutral or negative bids.

![affinity_scores](./affinity_scores.png)

![affinity_scores_by_subject_area](./affinity_scores_by_subject_area.png)


## Reviewer Bids

For reviewer bids, we see that most of the assigned pairs have "Very High" bids from the reviewers, with the majority of the rest having "High" bids. Moreover, not a single pair has a negative bid. This indicates that reviewers are generally interested in the papers they are assigned to. Note that although we default missing bids to "Neutral", the number of matched pairs with "Missing" bids is larger than that of pairs with "Neutral" bids. This is because if a reviewer submitted their bids, they are most likely assigned to the papers they bid positively on. The matched pairs with "Missing" bids are usually those where reviewers did not submit their bids, and the assignment for them was purely based on the affinity scores.

![bid_distribution](./bid_distribution.png)

![bid_distribution_by_subject_area](./bid_distribution_by_subject_area.png)


## Reviewer Load

If we distribute the reviewer load evenly, reviewers should be assigned to a mean of $4.42$ papers. However, as the assignment algorithm aims for high-quality assignments, the majority of reviewers were assigned to $6$ papers, the limit we set for reviewers. 

![reviewer_load_distribution](./reviewer_load_distribution.png)

Nevertheless, some reviewers in the pool are not assigned to any papers or are assigned to only one paper. After analyzing the data more carefully, we found that most of these reviewers either had no known affinity scores with the papers (mostly because they did not have any past work on OpenReview) or did not submit their bids. Moreover, there are even $50$ reviewers who had neither affinity scores nor bids. Therefore, it is hard for the algorithm to find good matches for them.

We suggest that reviewers submit their bids and provide more information about their past work to help the algorithm find better matches for them.

![reviewer_load_distribution_by_type](./reviewer_load_distribution_by_type.png)


While the reviewer load distribution for each subject area generally follows the overall distribution, we note that some subject areas, like Bandits, have a notably higher number of papers assigned to each reviewer. In fact, most reviewers in the Bandits area were assigned to $6$ papers. This indicates that for these areas, we will need to work harder to recruit more reviewers in future conferences.

![reviewer_load_distribution_by_subject_area](./reviewer_load_distribution_by_subject_area.png)



## Reviewer Confidence

In the review process, reviewers were asked to provide their confidence in their reviews on a scale from $1$ to $5$. A higher value means the reviewer is more confident. The distribution of reviewer confidence is shown below. Here, a confidence of $-1$ means that the matched pair was adjusted manually by the area chairs, and a confidence of $0$ means that the reviewer did not submit their review. We can see that among the pairs where the reviewer completed the review, most matched pairs have a confidence of $3$ or higher. This indicates that reviewers are generally confident in their reviews.

![confidence_distribution](./confidence_distribution.png)

On a side note, we found that reviewer confidence is generally lower for theoretical areas like Algorithmic Game Theory, Bandits, Causal Inference, and Learning Theory, while it is higher for other areas. It is hard to explain this phenomenon exactly, but we think this might be because the difficulty of reviewing papers in theoretical areas is generally higher, leading reviewers to be more cautious in their reviews.

![confidence_distribution_by_subject_area](./confidence_distribution_by_subject_area.png)



# Comparison with the Default Algorithm

Besides analyzing the deployed assignment, it is also natural to ask how the new algorithm PM compares to the default algorithm used in OpenReview, i.e., the maximum-quality assignment. To answer this question, we ran the default algorithm on the same data and compared the resulting assignment with the deployed assignment. Below, we show the comparison with the default algorithm in aggregate scores, reviewer bids, and reviewer load.

## Aggregate Scores

In terms of aggregate scores, the default algorithm achieved a mean of $1.53$, while PM achieved a mean of $1.50$, which is about $98$% of that of the default algorithm. Note that the default algorithm is optimal in quality, so any other algorithm will have a lower quality, and the difference is expected.

![aggregate_scores_with_default](./aggregate_scores_with_default.png)



## Reviewer Bids

How do the sampled assignments resulting from the new algorithm differ from the default one? Here we show the distribution of reviewer bids in the default assignment, the overlap between the optimal deterministic assignment and the deployed assignment, and the overlap between the optimal deterministic assignment and three sampled assignments from PM. As seen in the following figure, a non-negligible number of matched pairs have changed from the default assignment to the deployed assignment, and over half of the matched pairs would be different in three samples from PM. This indicates that PM introduces a good amount of randomness into the assignment, increasing robustness against malicious behavior while incurring only a small loss in matching quality.

![bid_distribution_by_algorithm](./bid_distribution_by_algorithm.png)



## Reviewer Load

Another side benefit of PM is that it can help distribute the reviewer load more evenly. In the following figure, we show the distribution of reviewer load in the optimal deterministic assignment and the deployed assignment. We can see that both the number of reviewers assigned to $6$ papers and the number of reviewers assigned to $0$ papers are reduced in the deployed assignment compared to the optimal one. To ensure an even more balanced reviewer load, additional constraints on the minimum number of papers per reviewer could be added in the future.

![reviewer_load_distribution_with_default](./reviewer_load_distribution_with_default.png)


# Conclusion

In this post, we introduced the paper assignment algorithm used for NeurIPS 2024 and explained how we implemented it. We analyzed the results of the assignment and compared it with the default algorithm used in OpenReview. We found that the assignment produced by the new algorithm achieved high-quality matches, with a good amount of randomness introduced into the assignment, increasing robustness against malicious behavior as well as enhancing reviewer diversity and anonymity. In future conferences, we suggest that reviewers submit their bids and provide more information about their past work to help the algorithm find better matches for them.

# Acknowledgments

We extend our sincere gratitude to the NeurIPS 2024 organizing committee for their trust and support in deploying the new assignment algorithm. We also thank program chairs Jakub Tomczak, Cheng Zhang, Ulrich Paquet, and Danielle Belgrave, along with workflow manager Zhenyu Sherry Xue, for their invaluable assistance throughout the assignment process.

# References

[1] Xu, Yixuan Even, Steven Jecmen, Zimeng Song, and Fei Fang. "A One-Size-Fits-All Approach to Improving Randomness in Paper Assignment." *Advances in Neural Information Processing Systems* 36 (2024).

[2] Charlin, Laurent, and Richard Zemel. "The Toronto paper matching system: an automated paper-reviewer assignment system." (2013).

[3] Stelmakh, Ivan, Nihar Shah, and Aarti Singh. "PeerReview4All: Fair and accurate reviewer assignment in peer review." *Journal of Machine Learning Research* 22.163 (2021): 1-66.

[4] Jecmen, Steven, Hanrui Zhang, Ryan Liu, Fei Fang, Vincent Conitzer, Nihar B. Shah. "Near-optimal reviewer splitting in two-phase paper reviewing and conference experiment design." *Proceedings of the AAAI Conference on Human Computation and Crowdsourcing*. Vol. 10. 2022.

[5] Tang, Wenbin, Jie Tang, and Chenhao Tan. "Expertise matching via constraint-based optimization." *2010 IEEE/WIC/ACM International Conference on Web Intelligence and Intelligent Agent Technology*. Vol. 1. IEEE, 2010.

[6] Flach, Peter A., Sebastian Spiegler, Bruno Golenia, Simon Price, John Guiver, Ralf Herbrich, Thore Graepel and Mohammed J. Zaki. "Novel tools to streamline the conference review process: Experiences from SIGKDD'09." *ACM SIGKDD Explorations Newsletter* 11.2 (2010): 63-67.

[7] Taylor, Camillo J. "On the optimal assignment of conference papers to reviewers." *University of Pennsylvania Department of Computer and Information Science Technical Report* 1.1 (2008): 3-1.

[8] Charlin, Laurent, Richard S. Zemel, and Craig Boutilier. "A Framework for Optimizing Paper Matching." *UAI*. Vol. 11. 2011.

[9] Shah, Nihar B. "Challenges, experiments, and computational solutions in peer review." *Communications of the ACM* 65.6 (2022): 76-87.

[10] Mimno, David, and Andrew McCallum. "Expertise modeling for matching papers with reviewers." *Proceedings of the 13th ACM SIGKDD international conference on Knowledge discovery and data mining*. 2007.

[11] Liu, Xiang, Torsten Suel, and Nasir Memon. "A robust model for paper reviewer assignment." *Proceedings of the 8th ACM Conference on Recommender systems*. 2014.

[12] Rodriguez, Marko A., and Johan Bollen. "An algorithm to determine peer-reviewers." *Proceedings of the 17th ACM conference on Information and knowledge management*. 2008.

[13] Tran, Hong Diep, Guillaume Cabanac, and Gilles Hubert. "Expert suggestion for conference program committees." *2017 11th International Conference on Research Challenges in Information Science (RCIS)*. IEEE, 2017.

[14] Goldsmith, Judy, and Robert H. Sloan. "The AI conference paper assignment problem." *Proc. AAAI Workshop on Preference Handling for Artificial Intelligence*, Vancouver. 2007.

[15] Vijaykumar, T. N. "Potential organized fraud in ACM." *IEEE computer architecture conferences*. Online [https://medium.com/@tnvijayk/potential-organized-fraud-in-acm-ieee-computer-architecture-conferences-ccd61169370d](https://medium.com/@tnvijayk/potential-organized-fraud-in-acm-ieee-computer-architecture-conferences-ccd61169370d) Last accessed April. Vol. 4. 2020.

[16] Littman, Michael L. "Collusion rings threaten the integrity of computer science research." *Communications of the ACM* 64.6 (2021): 43-44.

[17] Jecmen, Steven, Hanrui Zhang, Ryan Liu, Nihar B. Shah, Vincent Conitzer and Fei Fang. "Mitigating manipulation in peer review via randomized reviewer assignments." *Advances in Neural Information Processing Systems* 33 (2020): 12533-12545.

[18] Budish, Eric, Yeon-Koo Che, Fuhito Kojima and Paul Milgrom. "Implementing random assignments: A generalization of the Birkhoff-von Neumann theorem." *Cowles Summer Conference*. Vol. 2. No. 2.1. 2009.

[19] Gurobi Optimization, LLC. *Gurobi Optimizer Reference Manual*, 2023.