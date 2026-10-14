+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "Incentives in Heart Transplant Allocation"
# Date must be written in YYYY-MM-DD format.
date = 2026-10-14

[taxonomies]
areas = ["Artificial Intelligence", "Theory"]
tags = ["Game Theory", "Mechanism Design", "Organ Allocation", "Strategic Classification"]

[extra]
author = {name = "Ioannis Anagnostides", url = "https://www.andrew.cmu.edu/user/ianagnos/" }
committee = [
    {name = "Justine Sherry", url = "https://www.justinesherry.com/"},
    {name = "Vincent Conitzer", url = "https://www.cs.cmu.edu/~conitzer/"},
    {name = "Emanuel Tewolde", url = "https://emanueltewolde.com/"}
]
+++

# Introduction

The allocation of scarce donor organs constitutes one of the most consequential algorithmic problems in healthcare. Organ transplantation remains in many cases the only viable option for critically ill patients. Unfortunately, demand far outweighs existing supply: in the United States alone, more than 100,000 patients are currently on the waitlist.


For decades, the mechanisms governing organ allocation were rigid, rule-based priority systems handcrafted primarily by medical committees comprising domain experts. However, as the complexity of patient data rapidly grows and the pressure to improve efficiency intensifies, there is a widespread push to leverage machine learning and data-driven optimization approaches to improve decision making. Many such approaches based on sophisticated algorithms have already been deployed in practice.

But to fully reap the rewards promised by these advances, we must account for a fundamental and often overlooked factor: _incentives_. In game theory, a “game” describes a system in which rules shape the decisions of multiple actors, who may change their behavior to improve their outcomes. Organ allocation is such a game: patients, clinicians, transplant centers, and organ procurement organizations (OPOs), which coordinate the recovery and allocation of deceased-donor organs, all respond to allocation policies. This makes organ allocation a game-theoretic problem, not merely an optimization problem based on historical data.

When a donor organ becomes available, the allocation system produces a ranked list of compatible candidates. The OPO offers the organ to transplant centers in that order, and each center decides whether to accept it for its candidate.

We examine four ways in which organ allocation policies shape behavior:

1. priority rules can influence clinicians’ treatment decisions;
2. discretionary allocation can influence how OPOs place organs;
3. performance monitoring can influence whether transplant centers accept offers; and
4. waitlist rules can influence which patients centers list or delist.

For each case, we describe the policy, the behavioral response it creates, and possible changes that could better align incentives.


# Patient feature manipulation {#patient-feature-manipulation}

## Background

The US heart transplant allocation policy ranks candidates according to medical urgency. Before 2018, it divided candidates among three tiers: Status 1A, Status 1B, and Status 2. In 2018, these were replaced by six statuses, with Status 1 representing the highest priority. The new system was intended to distinguish more precisely among candidates with different conditions and forms of medical support. Because a patient’s status is based partly on the treatment and medical support they receive, status rules can also influence clinicians’ treatment decisions.

## The device game

The 2018 policy’s treatment of device usage provides an illustrative example. Patients bridged with an intra-aortic balloon pump (IABP), a temporary device that helps the heart pump blood, were designated Status 2, giving them relatively high priority. Conversely, patients supported with a left ventricular assist device (LVAD), a mechanical pump that supports the heart, have reduced priority to Status 4; compared to the prior allocation policy, this is a lower priority. It turns out that the proportion of patients bridged with an IABP increased significantly following the adoption of the new policy from 7.0% to 24.9%; this is more than a threefold increase. The concern here is that the policy change triggered a shift in the selection of recipients for bridging with IABP. Notwithstanding the potential benefits and legitimate medical reasons, using IABP has certain adverse effects, such as risk of reduced blood flow to internal organs. Complications involving serious bleeding have also been associated with longer duration of IABP support. While clinical practice has shifted toward more advanced devices, the incentive structure and strategic dilemma remain intact.

Goodhart's law succinctly explains the fundamental problem: "When a measure becomes a target, it ceases to be a good measure."

## Policy optimization going forward

There are growing calls to move away from the current 6-tier system as it fails to sufficiently account for pretransplant and post-transplant survival. One proposed way to account for these outcomes more directly is _continuous distribution_, a scoring system comprising multiple factors. This framework was recently deployed in US lung transplant allocation and is currently being extended to heart allocation. This mitigates cliff edge effects of tier boundaries, where a marginal change in therapy leads to a considerable priority upgrade. Still, misreporting of the form highlighted earlier remains possible since the underlying classification or regression algorithms on which continuous distribution relies are not impervious to feature manipulation.

## Connection to strategic classification

From a broader standpoint, this problem has recently garnered considerable attention at the intersection of machine learning and game theory, and is known as _strategic classification_. In strategic classification, there are certain features that can be strategically misreported in order to elevate the chance of being classified favorably (see Figure 1). A canonical motivating application in that framework is predicting credit default risk. What makes this problem interesting is that there is a cost to misreporting, especially when the reported feature is far from the ground truth, so optimal manipulation needs to carefully balance between two conflicting objectives.

Feature manipulation is not just about device usage, but has broader manifestations. An example concerns the amount of time a patient spent on the waitlist. The current allocation policy prioritizes patients who have been on the waitlist longer, at least without a status change. This creates a possible incentive for centers to list patients early, perhaps earlier than what is medically necessary.

What can be done to combat feature manipulation? One obvious remedy is to build machine learning models that rely less on, or at least make more judicious use of, manipulable features, such as device utilization. Another way to mitigate the problem is to increase the cost of manipulation. One feasible way could be through the use of _randomized audits_. In mechanism design, this approach is called _selective verification_, and is known to be effective in aligning incentives even with a small number of verifications.

It is important to note that the current system already requires clinicians to justify device usage with evidence based on physiological measurements, but device choices can still respond to the incentives created by status rules.

<p align="center">
  <img src="./strat_class.png"
       alt="Strategic classification in organ allocation"
       width="550">
</p>

<p align="center">
  <em>
    Figure 1: Strategic classification in organ allocation. Patients with feature vectors below the threshold (red region) incur a cost to manipulate certain features (e.g., device implantation) to cross the decision boundary and gain high priority status (green region), gaming the classifier.
  </em>
</p>

# Open offers and out-of-sequence allocation {#open-offers-and-out-of-sequence-allocation}

## How out-of-sequence allocation works

While the US allocation algorithm is designed to be a rigid priority queue based on factors such as medical urgency and geographic proximity, in practice, it operates alongside a discretionary mechanism known as _out-of-sequence_ allocation.

In particular, the official policy authorizes OPOs to bypass the match run if it is ascertained that there is a risk of organ loss. The match run is the ranked list of potential recipients generated for a donated organ; bypassing it allows an OPO to allocate the organ directly to a specific center. Organs deteriorate with the passage of time. Therefore, traversing a long list of offers can result in a significant time delay; issuing even a single offer requires considerable logistical effort and precious time. To accelerate this process, OPOs may resort to _open offers_, broadcasting the organ's availability to multiple centers simultaneously.

Although this pathway of out-of-sequence allocation afforded to the OPOs may be necessary in certain instances to prevent organ wastage, the threshold to trigger it is opaque and subjective. Unlike the allocation policy, the rules of which are entirely transparent, the out-of-sequence mechanism relies on the judgment of individual OPOs.

## Why OPOs use open offers

Why would an OPO choose to bypass the priority queue even when there is no medical urgency to do so? One reason is that OPOs are incentivized to maximize the number of organs placed while minimizing logistical effort. Out-of-sequence allocation can be significantly more efficient than making sequential offers in a short time window. Another factor is the center's relationship with the OPO, creating conditions under which collusion can emerge. We see again that failing to account for incentives can induce unexpected behavior.

A recent [investigation by the New York Times](https://www.nytimes.com/interactive/2025/02/26/us/organ-transplants-waiting-list-skipped-patients.html) poignantly documented the rapid growth of open offers, describing the current organ transplant system as being in "chaos." Although out-of-sequence allocation was a rare exception in the past (on the order of 1%), the number of out-of-sequence allocations has skyrocketed in recent years. Across all organs, approximately 19% of allocations in 2023 were classified as out-of-sequence. At the same time, the number of discarded organs has also increased, casting doubt on the claim that such discretion is necessary to prevent organ discard. Another concerning finding is that out-of-sequence allocations predominantly favor certain demographic groups, typically more affluent individuals.

Recent developments demonstrate that OPOs do respond rapidly to changes in policy and monitoring. Following federal scrutiny of OPOs' out-of-sequence allocations starting in 2025, the rate of such exceptions plummeted from 20% in 2024 to 9% by early 2026.

## Improving transparency

The remedy to mitigate out-of-sequence allocations is to bring more transparency to the decision making, to help ensure that OPOs use this option only when medically necessary. Furthermore, should an open offer be deemed the best course of action, open offers should still adhere to a localized, compressed policy that is transparent—for example, broadcast to all centers within a certain distance—rather than allowing direct, manual placement to specific favored centers.

<p align="center">
  <img src="./oos.png" alt="Out-of-sequence allocation flowchart" width="550">
</p>

<p align="center"><em>Figure 2: The logic of out-of-sequence allocation. The red arrow shows the resulting placement with a candidate outside the priority order; the preceding broadcast to multiple centers is not depicted.</em></p>


# Strategic offer rejection and performance monitoring {#strategic-offer-rejection-and-performance-monitoring}

Once an offer is issued—whether in accordance with the national policy's priority queue or an out-of-sequence offer—the transplant center has the option of rejecting that offer. This decision is made by a medical committee that weighs whether the proposed match is viable. Now, the reality is that centers have their own distinct incentives, and there are concerns that centers may end up rejecting viable offers or accepting offers that are not the best for the patient in expectation, contributing to system inefficiency (including organ wastage in the case of rejected offers).

We argue that a primary force driving this behavior is the performance monitoring regime. Transplant centers are evaluated semi-annually by the Scientific Registry of Transplant Recipients (SRTR). These program-specific reports publicly rate centers on a 5-tier system. The evaluation is based on three key metrics: survival on the waiting list (pre-transplant mortality rate), getting a transplant faster (transplant rate), and 1-year organ survival (whether the transplanted organ, or graft, continues to function for one year). The result is that centers operate under the constant pressure of regulatory flagging; a poor evaluation can lead to loss of insurance contracts or even revocation of certification.

## The pitfalls of performance monitoring

Although performance monitoring can increase accountability and drive continuous quality improvement, it is unclear whether the current system achieves those goals. There are concerns that the current regime incentivizes risk aversion. From the center's perspective, accepting an organ poses an asymmetric risk: a successful operation results in a marginal gain in volume, but an unsuccessful one can disproportionately undermine the center's metrics. Transplant outcomes also depend on the recipient’s clinical risk. While SRTR does use an estimated score function to adjust the evaluation for different levels of risk in different cases, it is not clear whether it is sufficient; if not, there is an incentive to admit easier cases and not difficult ones. The existing evaluation system may also not accurately reflect the key metrics of interest. For example, focusing on 1-year organ survival disregards longer-term outcomes, which are arguably more informative when it comes to determining the efficiency of the system. The key reason behind the prevalent use of short-term metrics, such as 1- or 3-year outcomes, is practical: they provide timely feedback necessary for rapid performance evaluation. However, this may be at odds with the objective of maximizing total life years gained.

### Evaluation cycle gaming

Moreover, the temporal nature of evaluations may distort incentives. Horizon effects can force centers to become hyper-conservative as the reporting window closes in order to protect their current standing. Conversely, a center with a guaranteed top-tier evaluation may be inclined to take more risks in order to conduct more transplants and thus to make more profit. A center just below an evaluation threshold may likewise take more risks in hopes of crossing it. Such distortion is not unique to organ allocation. For example, agents altering their risk tolerance as the reporting horizon comes to a close—becoming risk-averse to lock in a superior standing or risk-seeking to gamble for resurrection—is well-documented in financial markets. Similar gaming is common in sports toward the end of a match.

The disconcerting reality is that an overwhelming proportion of offers end up being rejected. Offer rejection triggers a vicious cycle where delays degrade organ quality, making subsequent rejection and ultimate discard more likely. The high organ discard ratio may be exacerbated by the current evaluation system.

## Improving performance evaluation

To be clear, we are not arguing that performance evaluation should be eliminated; rather, we emphasize the need to refine current evaluation mechanisms to mitigate unintended consequences. Machine learning can again empower the development of more accurate risk adjustment models in particular, and better evaluation systems in general. Also, moving away from the rigid semi-annual evaluation system to a continuous monitoring system would reduce the incentive to game the evaluation cycle.

The fact that there are so many rejections can also be attributed to the poor priority list created by the existing policy. Viewed from that perspective, one can argue that offer rejections serve to correct the inefficiency of the global policy. If this is the case, improving the allocation algorithm would have the concomitant effect of moderating offer rejections. Encouragingly, a wide array of emerging machine learning and data-driven algorithms are poised for deployment to address these challenges. Going forward, one approach, whose implementation would admittedly face considerable obstacles, is to remove the option from centers to reject offers. A more realistic alternative would be to penalize excessive turndowns of viable organs, or, conversely, to come up with credit score systems that incentivize centers to accept more offers.

# Strategic delisting and listing {#strategic-delisting-and-listing}

## How monitoring shapes the waitlist

Strategic incentives can also distort the composition of the waitlist itself, driving both the initial selection of candidates and the preemptive delisting of high-risk patients.

Before a patient qualifies to enter the waitlist, and thus becomes subject to SRTR monitoring, they must be admitted by an internal selection committee. This decision relies, in part, on subjective criteria. In particular, the performance monitoring regime described earlier creates an incentive for centers to curate their waitlist admissions so as to maximize survival rates and minimize waitlist mortality. Although subsequent deaths may appear in mortality records, regulators cannot determine from waitlist data which patients were evaluated but not listed or why.

Conversely, centers have an incentive to preemptively _delist_ quickly deteriorating patients by designating them "too sick to transplant." In this way, the center can prevent the death from being attributed to its program performance by removing high-risk candidates before a terminal event occurs. Unlike pre-listing selection, delisting is an explicit outcome measurement in the United Network for Organ Sharing (UNOS) system. This type of strategic behavior constitutes a form of data censoring: it can distort the center's metrics, and potentially deny candidates a chance at a life-saving procedure.

Among UNOS heart transplant candidates from 2010 to 2024, we find that approximately 20% are removed from the waitlist for reasons other than transplant or death. More than a third of these candidates were removed because the center deemed them too sick, while nearly another third were removed under the generic category of "Other." The latter category captures any patient not fitting into designated codes, rendering the specific reasons for removal in this group effectively unverifiable. We highlight this opacity as a major limitation of the current reporting, as it precludes a factual determination of the fate of these individuals.

To mitigate these adverse effects, we argue that the field must transition toward objective and transparent criteria for both listing and delisting.

## Multi-listing

Multi-listing occurs when candidates register at multiple centers, exploiting regional supply disparities or center acceptance criteria to increase transplant probability. While permissible, this creates severe equity concerns by correlating access with the ability to afford duplicate evaluations and travel–often via private aviation in order to be able to get to the center fast enough once an organ becomes available. This stratification is starkest in _transplant tourism_, where wealthy foreign nationals multi-list in the US. International patients pay premium rates–typically millions of dollars–making them financially attractive to centers seeking to maximize revenue. Multi-listing undermines the egalitarian values the allocation policy was designed to uphold.

Our analysis of UNOS adult heart transplant data from 2010 to 2024 reveals the effect of multi-listing. While a niche practice, employed by only 2.16% of patients, multi-listed candidates achieve a disproportionately higher transplant rate (80.44\% vs. 73.06\%). Notably, the median wait time drops sharply once a second listing is activated. The mean distance between centers for multi-listed candidates is 379 nautical miles (NM), roughly the distance between Boston and Washington, D.C., though the maximum exceeds 2,200 NM, representing cross-country listings. We observe a clear relationship between distance and outcomes. As the geographic spread between centers increases, transplant rates rise. Access to entirely different donor pools provides a substantial allocation advantage. These patients also exhibit a paradoxical clinical profile: they often hold higher urgency status yet suffer lower waitlist mortality, despite enduring longer wait times. This may partly reflect selection: candidates who multi-list must be healthy enough to travel between centers.

Transitioning to a single-entry mechanism would neutralize the inequitable advantage of multi-listing. However, multi-listing involves a tradeoff between fairness and efficiency. There may be cases–such as urgent or hard-to-match patients–where multi-listing improves the overall outcomes of the system.

# Conclusions

The transition from rule-based priorities to data-driven optimization represents a paradigm shift in organ allocation. However, algorithmic sophistication alone is insufficient. Treating allocation as a learning and optimization problem fails to account for the strategic behavior of agents operating within the system. We laid out many problems that are prevalent in today's transplant system, with a special focus on hearts. The path forward demands incentive-aware policy optimization.

The recent erosion of public confidence in the current deceased-donor organ allocation system [led to a significant drop in registered donors](https://www.nytimes.com/2026/01/23/us/organ-donation.html). This underscores another reality: aligning incentives is not just about increasing efficiency and equity; it is also the safeguard of public trust. In a system reliant on altruistic donors, a loss of trust is a loss of supply. Ultimately, saving more lives requires not just better algorithms, but better games.
