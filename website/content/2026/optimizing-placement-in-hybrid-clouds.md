+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "Moirai: Optimizing Placement of Data and Compute in Hybrid Clouds"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2026-07-09

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Systems"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
# Consider these similar to keywords specified for a research paper.
tags = ["cloud computing", "optimization", "cost"]

[extra]
author = {name = "Ziyue Qiu", url = "https://ziyueqiu.github.io/" }
# The committee specification is  a list of objects similar to the author.
committee = [
    {name = "Mingkuan Xu", url = "https://mingkuan.taichi.graphics"},
    {name = "Jignesh M. Patel", url = "https://jigneshpatel.org/"},
    {name = "David Andersen", url = "https://www.cs.cmu.edu/~dga/"}
]
+++

# Introduction

Hybrid cloud setups, combining on-premises datacenters and public cloud resources, have become increasingly common as enterprises seek scalability, flexibility, and cost benefits. However, this strategy introduces significant challenges, especially regarding where to store data and execute computational tasks (jobs). Unoptimized placement decisions can lead to unexpectedly high cloud bills, dominated primarily by egress fees—the costs incurred from transferring data out of the cloud.

Our research tackles this challenge with Moirai, a framework purpose-built to optimize data and compute placement in hybrid clouds. By leveraging fine-grained dependency analysis and strategic replication, Moirai delivers dramatic operational cost savings—reducing expenses by over 95% compared to the state-of-the-art solution, Alibaba’s [Yugong](https://dl.acm.org/doi/abs/10.14778/3352063.3352132).

# Understanding Hybrid Cloud Costs

Hybrid clouds combine the benefits of private (on-premises) datacenters and public clouds. Enterprises use hybrid clouds for reasons such as regulatory compliance, disaster recovery, and incremental migration to the cloud. However, effective use of hybrid clouds requires careful coordination of three key elements: jobs, datasets, and network bandwidth.

The Moirai implementation targets large-scale data analytics, so **jobs** correspond to analytics queries and **datasets** are the data units they operate on (e.g., database tables).
While we target analytics workloads over tabular data, the underlying logic applies broadly to other definitions of compute and data units.

![understanding](understanding_cloud.png)

_Figure 1: Hybrid cloud environment illustration, highlighting cost factors of job execution (compute), data storage, and data transfer between on-premises and public cloud._

**Jobs** can be executed either on-premises or in the cloud. While cloud execution offers flexible scaling through a pay-as-you-go model, on-premises resources are typically provisioned and paid for upfront, so it is generally preferable to utilize on-premises compute when possible. However, it is important to note that on-premises reads from cloud-stored data (and, less commonly, cloud writes to on-premises storage) can trigger significant egress fees due to data transfer out of the cloud. These costs can quickly escalate if placement decisions are not carefully managed.

**Datasets** can be stored on-premises, in the cloud, or replicated across both environments. Data replication can reduce the cost associated with remote data access but increases cloud storage expenses, typically charged based on the volume of data stored and duration of storage.

**Network** costs comprise fixed fees for leased dedicated bandwidth and variable egress fees based on data usage. Note that ingress, data transfer into cloud, is typically free. Among these, egress charges—fees incurred when transferring data from the cloud to on-premises—often dominate due to their per-byte billing model and prohibitive pricing.

## Public Cloud Pricing Comparison

To illustrate the importance of optimizing hybrid cloud usage, let's examine the pricing structures of three major public cloud providers:

| Service                        | AWS   | Azure | GCP   |
| ------------------------------ | ----- | ----- | ----- |
| Dedicated 100Gbps link (/hour) | $22.5 | $47.2 | $23.3 |
| Egress traffic (/GB)           | 2.0¢  | 2.5¢  | 2.0¢  |
| Object storage (/GB-month)     | 2.1¢  | 1.7¢  | 2.3¢  |

_Table 1: Pricing of three public cloud providers. Egress to Internet prices are based on the N. Virginia region. Dedicated link prices apply to connections within North America._


The table above highlights the significance of cloud egress fees, dedicated network bandwidth costs, and storage charges. Even seemingly minor per-byte charges quickly accumulate into substantial expenses when scaled to enterprise-level data analytics workloads.

## A Real-World Example: Uber’s Hybrid Cloud Migration (Hypothetical Scenario)

To illustrate the practical impact of hybrid cloud cost optimization, let’s consider a **hypothetical scenario** inspired by Uber’s ongoing migration of its batch analytics stack to GCP. Uber’s batch workloads—comprising large-scale analytics queries over massive datasets (i.e., database tables in Uber context)—are representative of the challenges faced by enterprises transitioning to hybrid cloud environments. The access patterns and operational requirements observed in Uber’s migration remain central to how costs and placement decisions are managed.

Assuming a migration where **approximately half** of Uber’s infrastructure has moved to the public cloud, and **hypothetically** that batch workloads require around **800,000 CPU cores**, the weekly cost breakdown (using GCP pricing) is as follows:

- **Storage**: 150 PiB of cloud storage incurs weekly charges of approximately **$900K**.
- **Compute**: 400,000 CPU cores in the cloud account for roughly **$2.28M** weekly.
- **Egress**: Data transfer out of the cloud, totaling around 250 PiB per week, dominates the cost profile at about **$5.25M** weekly.
  - The 250 PiB weekly egress arises from a total weekly data movement of about 1 EiB. If data is randomly distributed between cloud and on-premises storage, approximately one-fourth becomes egress traffic.
- **Dedicated Network Link**: Leasing a dedicated 3.5 Tbps network link adds another **$140K** weekly, assuming full utilization.

This hypothetical breakdown illustrates how workload access patterns and placement strategies can dramatically impact hybrid cloud costs. Notably, egress fees account for the largest share of expenses, emphasizing the need for strategic optimization of data and compute placement—precisely the challenge addressed by frameworks like Moirai.

## Consequences of Unoptimized Placement

Poorly optimized placement strategies exacerbate these costs. Consider a scenario where datasets A and B are separately placed—A on-premises and B in the cloud. Executing jobs that access both datasets becomes costly due to remote data access:

- Running a job on-premises that reads cloud-stored data triggers expensive cloud egress charges.
- Running the job in the cloud, conversely, requires either moving on-premises data (incurring network usage) or replicating it in the cloud (incurring additional storage costs).

Thus, effective placement requires joint optimization of jobs and datasets, considering their dependencies and access patterns.

# Introducing Moirai: Optimized Data and Compute Placement

To tackle these complexities, we introduce **Moirai**, a cost-optimization framework specifically designed for hybrid cloud environments. Moirai formulates the placement of data and compute as a Mixed Integer Programming (MIP) optimization problem, explicitly considering cloud egress fees, storage costs, and dedicated network link expenses. While the full mathematical formulation is omitted here, it's relatively straightforward to define the optimization problem itself. The critical challenge, however, is making it scale effectively to handle millions of jobs and tables weekly—an inherently NP-hard problem. Since Uber’s analytics workloads operate at the database table level, we will refer to tables rather than datasets for clarity throughout the remainder of this post.

## How Moirai Works

At Uber, a typical weekly workload involves over 4 million jobs and more than 1 million tables, resulting in a job–data dependency graph with millions of edges. Optimizing hybrid cloud placement can be viewed as finding a minimum cut on this graph. To make optimization tractable at this scale, Moirai applies three core heuristics that dramatically reduce problem complexity:

### 1. Grouping Similar Jobs
Job placement in hybrid clouds is fundamentally driven by data dependencies—specifically, (1) the location of tables a job accesses and (2) the volume of data transferred from each table. In practice, enterprise workloads exhibit recurring access patterns, where many jobs repeatedly access the same sets of tables in similar ways. This means that jobs often share both their data dependencies and the amount of data they access, forming natural groups.

Moirai leverages this observation by grouping jobs with identical recurring data access patterns into logical units. To achieve this, Moirai uses the concept of an analytics query **template**: the canonical logical plan of a query after removing constants (literals, predicates, `LIMIT` values), leaving only operators and fully-qualified table names. By hashing this canonical string into a 128-bit fingerprint, Moirai identifies jobs that share the same template—and thus the same set of dependencies and similar access patterns. This grouping reduces the number of unique job decisions from millions to hundreds of thousands for Uber in the weekly window, dramatically accelerating the optimization process while preserving accuracy.

### 2. Grouping Inactive Tables
Tables that remain unused over short periods (e.g., a week) are grouped together, substantially shrinking the table count from millions to tens of thousands. The grouping preserves optimization accuracy, as
the untouched tables remain isolated in the job–data dependency graph regardless of how they are grouped.

### 3. Preselecting Key Replicated Tables
Although the first two heuristics efficiently reduce problem size by one to two orders of magnitude, into a problem with 356K logical jobs and 134K logical tables, solving the optimization problem can still take over a week using weekly workload traces. For practical deployment, offline optimization must finish within the operational window (7 days here), and ideally within a few hours to accommodate on-demand requests.

To speedup the optimization, Moirai pre-selects tables for replication before optimization. This simplifies the job–data graph by removing job–data edges and isolating some job nodes, which speeds up optimization, as shown below.

![replication](./replication.png)

_Figure 2: Illustration of Moirai's heuristic reduction of optimization complexity, showing how selectively replicating popular tables significantly simplify the optimization process._

The main challenge is selecting tables that accelerate optimization with minimal impact on accuracy. To decide which tables to pre-select for replication, Moirai ranks tables based an array of metrics.
We evaluated five different metrics to identify the most efficient one for optimization:
- Access Traffic Volume: total bytes accessed for each table
- Job Access Frequency: number of jobs that access each table
- Inverse Dataset Size: inverse of the table size, highlighting smaller tables
- Access Traffic Density: bytes accessed normalized by the table size
- Job Access Density: number of jobs accessing a table normalized by the table size

To clarify the impact of each replication heuristic, we report the _effective_ scale of the job–data graph after pre-selecting tables for replication. This includes the number of edges, non-isolated jobs, and tables that remain for optimization. Figure 3 below illustrates how Moirai optimization time correlates with the reduced graph complexity for each heuristic.

![optimization-time](./optimization_time.png)

_Figure 3: Optimization time of Moirai and job–data graph complexity for various replication heuristics, evaluated over a week-long workload trace. The total size of pre-selected tables is fixed at 0.2% of overall data volume._

No Replication, which does not pre-select any table for replication, takes 147 hours on average. Access Traffic Volume requires 105 hours of optimization time, as it tends to allocate replication space to large tables based on traffic volume. This often results in insufficient trimming, overlooking tables with many dependencies relative to their size. Similarly, Inverse Dataset Size, which prioritizes replicating small tables regardless of access frequency, fails to reduce optimization time as it allocates replication quota to many small but cold tables. In contrast, heuristics that consider job connectivity, namely, Job Access Frequency and Job Access Density, are more effective, taking just 44 hours and 2 hours. As shown by the orange bars in Figure 3, they reduce the number of edges by 39% and 59% over No Replication.

Overall, Job Access Density performs best by considering both the table size and the number of job-data connections. Effectiveness is connected to the complexity of the job-data graph. Other metrics we evaluated do not consider the resulting graph edge count after table replication, while Job
Access Density picks small-but-widely-shared tables, maximizing edge reduction.

Therefore, Moirai uses Job Access Density as the metric for pre-selecting replication tables, reducing solution time from more than seven days to under two hours, making weekly updates practical.

## Online Routing Policy - Size Predict

While Moirai’s core focuses on offline optimization—periodically computing optimal placement for jobs and tables based on historical workload traces—it also requires **online routing** for new or ad-hoc jobs that arrive after the offline plan is computed. The online routing policy ensures that jobs not covered by the offline optimization are placed efficiently, minimizing incremental costs.

Moirai adopts a dependency-aware routing policy called **Size Predict** to minimize cross-site data access for newly-seen jobs. Most jobs declare their data dependencies (tables to read or write) before execution, but the actual data volume is only known during runtime. When a new job template appears, Size Predict estimates the access volume for each table using the mean volume from the previous window, then routes the job to the site (cloud or on-premises) where it is likely to process more data locally. If a table was not accessed in the previous window, its projected volume is treated as negligible, and placement is decided based on the other tables involved. This method outperforms simpler policies that ignore access size, since tables idle in one window rarely contribute significant traffic. By considering historical access patterns, Size Predict avoids the inefficiencies of naive routing strategies that disregard data placement and access behavior.

# Evaluation and Results

We evaluated Moirai using traces collected from Uber's large-scale data analytics platforms, specifically their Presto and Spark clusters, processing nearly 1EiB data weekly across more than two million jobs. Our evaluation compared Moirai against three baseline methods:

- **NoRep:** Data randomly partitioned without replication.
- **Rep3Mon:** Replicates the most recent three months of data; older data randomly partitioned.
- **Yugong (Alibaba):** Uses an MIP model but optimizes placement at the organizational level rather than at fine-grained job and table granularity. All jobs and data belong to a project should be placed in one site.

For a fair comparison, all approaches use Size Predict, which makes the baselines more competitive.

### Significant Cost Reduction

![eval](./eval.png)

_Figure 4: Weekly traffic and cost reduction between all baselines and Moirai._

Moirai demonstrated substantial advantages over all baselines:

- Reduced egress charges by over 99% compared to NoRep and Rep3Mon.
  - This highlights that replication alone is insufficient: strategic placement of remaining data is critical to minimize overall cost.
- Achieved **95% cost reduction** over Yugong.
  -  Significant inefficiency in Yugong is due to its dependence on project-level placement, which groups jobs and data based on human organizational boundaries rather than actual job-data dependencies, and constrains the flexibility of job scheduling.
- Significantly cut dedicated network infrastructure requirements.

These savings primarily stem from Moirai’s fine-grained optimization.

# Conclusion

Hybrid clouds offer substantial flexibility but come with intricate cost management challenges. Moirai addresses these through intelligent, dependency-driven optimization, achieving dramatic cost reductions and efficiency improvements at Uber-scale operations.

**Key Takeaways and Innovations:**

- **Fine-Grained Optimization:** Moirai’s approach of optimizing placement at the job and table level—rather than by organizational boundaries—demonstrates the power of data-driven, granular decision-making in large-scale systems.
- **Scalable Heuristics:** The use of grouping and pre-selection heuristics enables tractable optimization for millions of jobs and datasets, showing how practical systems can leverage patterns in real workloads.
- **Dependency Awareness:** By explicitly modeling job–data dependencies, Moirai avoids the inefficiencies of naive replication and placement, inspiring broader applications of dependency analysis in systems design.
- **Cost-Aware Design:** Moirai’s focus on real-world cost factors (egress, storage, network) highlights the importance of aligning system architecture with operational economics.

Moirai exemplifies how combining algorithmic rigor with practical heuristics can unlock new efficiencies in complex environments. Its innovations in scalable optimization and dependency modeling offer inspiration for tackling similar challenges in other domains, from distributed databases to edge computing.

As enterprises continue their hybrid cloud journeys, tools like Moirai become essential in managing complexity, reducing costs, and unlocking the true potential of hybrid cloud infrastructure.
