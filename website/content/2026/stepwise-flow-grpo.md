+++
title = "Crediting the Right Steps: Stepwise Reward Assignment for RL on Flow Matching Models"
date = 2026-05-04

[taxonomies]
areas = ["Artificial Intelligence"]
tags = ["reinforcement learning", "diffusion models", "flow matching", "credit assignment", "GRPO", "text-to-image generation"]

[extra]
author = {name = "Yash Savani", url = "https://yashsavani.com" }
committee = [
    {name = "Committee Member 1's Full Name", url = "Committee Member 1's page"},
    {name = "Committee Member 2's Full Name", url = "Committee Member 2's page"},
    {name = "Committee Member 3's Full Name", url = "Committee Member 3's page"}
]
+++

Flow matching models like Stable Diffusion 3.5 generate an image by iteratively denoising random noise over many small steps. When we want to fine-tune these models with reinforcement learning, say to make them follow text prompts more faithfully or produce more aesthetic outputs, a natural question arises: which steps deserve credit, or blame, for the final result?

The current state of the art, [Flow-GRPO](https://arxiv.org/abs/2505.05470), sidesteps this question. Every denoising step gets the same credit, computed from the reward on the final image. If the image is good, every step is reinforced equally. If it is bad, every step is penalized. This is a tempting simplification, but it ignores something important about how diffusion generation actually works. Different steps do fundamentally different things, and treating them identically wastes most of the available learning signal.

This blog post describes our recent work, [_Stepwise Credit Assignment for GRPO on Flow Matching Models_](https://stepwiseflowgrpo.com), which proposes a fix.

## TL; DR

- **Problem.** Flow-GRPO assigns the same advantage to every denoising step in a trajectory, ignoring that early steps determine composition while late steps refine details. A trajectory with bad early decisions that get corrected later is reinforced just as strongly as one with good decisions throughout.
- **Stepwise rewards via Tweedie.** We score every denoising step by applying the reward model to a one-step (or few-step) Tweedie estimate \\(\hat{x}\_{0}(t) = \mathbb{E}[x\_{0} \mid x\_{t}]\\) of the clean image. This is essentially free since \\(\hat{x}\_{0}(t)\\) reuses the predicted noise that the flow model already computes.
- **Stepwise gains, not raw rewards.** We optimize the per-step gain \\(g\_{t} = r\_{t-1} - r\_{t}\\). The gains telescope to the total reward improvement, so we get fine-grained credit assignment without changing the global objective.
- **Improved SDE.** Flow-GRPO's SDE injects enough noise that intermediate samples confuse the reward model. We replace it with a DDIM-inspired alternative that exactly preserves the marginal variance of rectified flow while still allowing exploration.
- **Results.** Stepwise-Flow-GRPO converges faster than Flow-GRPO on PickScore, ImageReward, and UnifiedReward, in both training iterations and wall-clock time. It trains stably where Flow-GRPO diverges (UnifiedReward, OCR rendering). After 400 GPU hours, it reaches **0.87 on GenEval**, beating GPT-4o (0.84).

![Two trajectories from the same prompt have similar final rewards but very different intermediate behavior. Trajectory 0 dips at t=0.86 before recovering, and trajectory 1 drops sharply at t=0.71. Uniform credit assignment treats them identically.](./figure1-motivation.png)

**Figure 1.** Two denoising trajectories from the same prompt reach roughly the same final reward (about 0.90), but they take very different paths. One has a clean monotone improvement; the other dips badly midway and recovers later. Flow-GRPO's uniform credit assignment cannot tell them apart. Stepwise-Flow-GRPO can, and uses that distinction to learn faster.

## Background

I will set up just enough background to make the rest of the post self-contained.

### Flow Matching

[Rectified flow](https://arxiv.org/abs/2209.03003) is a recent reframing of diffusion models that has become standard in state-of-the-art image generators. Given a clean data sample \\(x\_{0}\\) and noise \\(x\_{1} \sim \mathcal{N}(0, I)\\), it defines the linear interpolant \\(x\_{t} = (1-t)x\_{0} + tx\_{1}\\) for \\(t \in [0, 1]\\). A neural network \\(v\_{\theta}\\) is trained to predict the velocity \\(\dot{x}\_{t} = x\_{1} - x\_{0}\\) of this interpolant. To generate, we start at pure noise (\\(t=1\\)) and integrate the learned ODE \\(dx\_{t} = v\_{\theta}(x\_{t}, t, c) dt\\) backward to \\(t=0\\), yielding a clean image conditioned on prompt \\(c\\).

This deterministic ODE works well for inference, but RL needs stochasticity. We need different samples to compare. The standard trick is to convert the ODE into an SDE that has the same time marginals (a consequence of the Fokker-Planck equation). After Euler-Maruyama discretization, each step samples from a Gaussian:

\\[ \pi\_{\theta}(x\_{t-\Delta t} \mid x\_{t}, c) = \mathcal{N}(x\_{t-\Delta t};\ \mu\_{t},\ \sigma\_{t}^{2} \Delta t \cdot I) \\]

Now we have a stochastic policy we can optimize.

### GRPO

[GRPO](https://arxiv.org/abs/2402.03300) is the policy optimization algorithm popularized by [DeepSeek-R1](https://arxiv.org/abs/2501.12948). It is appealingly simple: for each prompt \\(c\\), sample \\(N\\) trajectories, compute each one's reward, and standardize within the group:

\\[ A^i = \frac{r^i - \mathrm{mean}}{\mathrm{std}} \\]

This group-relative advantage gets multiplied by a clipped propensity ratio and combined with a KL penalty against a reference policy, in the standard PPO style. The key feature is that there is no critic network and no value function, just relative comparisons within a group.

[Flow-GRPO](https://arxiv.org/abs/2505.05470) applies GRPO to flow matching by computing one reward per trajectory, on the final image, and propagating that single advantage \\(A^i\\) to every denoising step \\(t = 0, \dots, T-1\\). Every step in trajectory \\(i\\) sees the same advantage. This is the design choice we challenge.

## Why Uniform Credit Assignment is Wasteful

Flow-GRPO's uniform credit assignment fails for two related reasons.

**Problem 1: Diffusion has a temporal hierarchy.** Different denoising steps contribute fundamentally different information to the final image, and we can see this from a quick frequency-domain analysis. Natural images concentrate energy at low frequencies (their power spectra fall off as \\(|k|^{-\alpha}\\)), while Gaussian noise is flat across frequencies. The signal-to-noise ratio at frequency \\(k\\) and time \\(t\\) is therefore

\\[ \mathrm{SNR}\_{t}(k) = \left(\frac{1-t}{t}\right)^{2} \frac{1}{|k|^{\alpha}} \\]

The \\(1/|k|^\alpha\\) factor means low frequencies always have higher SNR than high frequencies. As denoising proceeds (\\(t \to 0\\)), the global \\(((1-t)/t)^2\\) prefactor grows, progressively lifting higher frequencies above the noise floor. The result is a coarse-to-fine generation order. At \\(t \approx 1\\), only low-frequency information is recoverable, so early steps determine layout and composition. Fine details emerge only near \\(t = 0\\). Rewarding both phases equally is like grading an essay's outline and its punctuation on the same rubric.

**Problem 2: Mistakes get rewarded if they get corrected.** Imagine a trajectory where the model commits to the wrong color at \\(t \approx 1\\) (say, magenta instead of orange), but later steps drift back to correct it. The final image looks fine, so Flow-GRPO reinforces every step in the trajectory, including the bad early decision. We want to penalize that early mistake, not bake it in.

Figure 1 above shows both problems empirically. Two trajectories with the same prompt reach similar final rewards, but they take very different routes. Uniform credit assignment is blind to this. The structure is exactly the kind of signal a smarter credit assignment scheme could exploit.

## Stepwise-Flow-GRPO

The plan is straightforward. Instead of one reward per trajectory, compute a reward at every step, and credit each step based on its *gain* over the previous step. The challenge is doing this without (1) running an expensive reward model on noisy intermediate states, and (2) introducing optimization pathologies that subvert the final objective.

### Estimating Intermediate Rewards via Tweedie's Formula

Reward models are trained on clean images. We cannot just feed them noisy intermediate states \\(x\_{t}\\); the result would be garbage. But Tweedie's formula gives us a posterior-mean estimate of the clean image:

\\[ \hat{x}\_{0}(t) := \mathbb{E}[x\_{0} \mid x\_{t}] = x\_{t} - t \hat{x}\_{1} \\]

where \\(\hat{x}\_{1}\\) is the predicted noise, already computed at every step during sampling. So a one-step Tweedie estimate is essentially **free**: it reuses computation we are already doing. In practice, we get sharper estimates by running a few extra ODE substeps from \\(x\_{t}\\) toward \\(x\_{0}\\). We use \\(T' = 5\\) substeps, which empirically gives strong reward signal at modest cost. An ablation in the paper shows the method is robust to this choice. Each Tweedie estimate is then scored by the reward model: \\(r\_{t}^{i} = R(\hat{x}\_{0}^{i}(t), c)\\).

Because the denoising from each \\(x\_{t}^{i}\\) is independent, all \\(T\\) reward estimates for a trajectory can be computed in parallel, which keeps the wall-clock overhead manageable.

### Gains, Not Raw Rewards

If we directly optimized intermediate rewards \\(r\_{t}^{i}\\), we would push the model toward producing high-scoring *Tweedie estimates* rather than high-scoring final images. That is the wrong objective. The fix is to optimize the **gain**:

\\[ g\_{t}^{i} := r\_{t-1}^{i} - r\_{t}^{i} \\]

i.e., the reward improvement from one step to the next. The crucial property is that gains telescope:

\\[ \sum\_{t=1}^{T} g\_{t}^{i} = r\_{0}^{i} - r\_{T}^{i} \\]

Maximizing the sum of gains is equivalent to maximizing the improvement from initial noise to final image. Since all \\(N\\) trajectories in a group share the same initial noise \\(x\_{T}\\), the term \\(r\_{T}^{i}\\) is constant within a group, and the *group-relative* sum of gains equals the *group-relative* final reward. We get local credit assignment for free without sacrificing the global objective.

![Mean absolute gain per denoising step, measured on 256 GenEval prompts using PickScore. Gains are largest near t=1 and shrink as t approaches 0.](./figure2-gain-magnitudes.png)

**Figure 2.** Mean absolute gain per denoising step, measured on 256 GenEval prompts using PickScore. Gains are largest near \\(t = 1\\) and shrink as denoising progresses. Most reward improvement comes from early compositional decisions, with later steps making smaller refinements. This matches the frequency-hierarchy story from earlier and gives the optimization a natural prior toward the steps that matter most.

### Joint Normalization

We compute group-relative advantages, but we normalize *jointly* across all steps and trajectories rather than per-step:

\\[ \tilde{A}\_{t}^{i} = \frac{g\_{t}^{i} - \mu\_{\text{global}}}{\sigma\_{\text{global}}} \\]

Why joint rather than per-step? Per-step normalization would inflate noise in late steps where reward changes are small, washing out the signal where it is meaningful. Joint normalization preserves the natural temporal structure: early gains are bigger, so they get bigger advantages, exactly as we want. An ablation in the paper confirms that joint normalization converges substantially faster.

### Pseudocode

The algorithm is essentially Flow-GRPO with the gain computation and joint normalization swapped in:

```python
# All N trajectories in a group share the same initial noise x_T
for i in range(N):
    x[i, T] = x_T
    for t in range(T-1, -1, -1):
        x[i, t] ~ pi_theta( . | x[i, t+1], c)               # SDE step
    for t in range(T):
        x_hat_0[i, t] = denoise(x[i, t], substeps=T_prime)  # Tweedie estimate
        r[i, t]       = R(x_hat_0[i, t], c)                 # reward at step t

# Stepwise gains
g[i, t] = r[i, t-1] - r[i, t]

# Joint normalization across all i, t
A_tilde = (g - mean(g)) / std(g)

# Standard GRPO update with A_tilde[i, t] instead of trajectory advantage A^i
optimize(theta, A_tilde, propensity_ratio, KL_penalty)
```

That is the entire method. The change from Flow-GRPO is small in code and large in effect.

### Connection to Adaptive Submodular Optimization

There is a clean theoretical motivation for greedy gain maximization. Recent work by [Kveton et al. (2025)](https://rlj.cs.umass.edu/2025/papers/RLJ_RLC_2025_193.html) showed that KL-regularized policy gradients on per-step gains learn near-optimal policies when reward gains are *monotone and submodular*, an analog of classic guarantees for greedy submodular maximization. In a simplified on-policy variant of our method (where the propensity ratio is 1 and advantages are replaced by raw gains), the objective reduces algebraically to theirs.

Our setting generalizes Kveton et al. to off-policy GRPO with group-relative advantages, and is the first application of adaptive gain maximization to flow models. We do not formally verify submodularity for the reward functions we use, but the diminishing gains in Figure 2 are consistent with submodular-like structure, and the empirical results suggest the analogy is doing real work.

## An Improved SDE: A Complementary Fix

There is a separate issue with Flow-GRPO that we noticed while developing stepwise credit assignment. Flow-GRPO's SDE injects enough noise that intermediate samples become visibly degraded compared to the deterministic ODE. Since reward models are trained on clean images, this degrades the reward signal regardless of the credit assignment scheme. So we replaced Flow-GRPO's SDE with a [DDIM](https://arxiv.org/abs/2010.02502)-inspired alternative.

The new update rule interpolates between deterministic and stochastic sampling:

\\[ x\_{t-\Delta t} = (1 - (t-\Delta t)) \hat{x}\_{0}(t) + \sqrt{(t-\Delta t)^{2} - \sigma\_{t}^{2}} \\, \hat{x}\_{1} + \sigma\_{t} \epsilon \\]

When \\(\sigma\_{t} = 0\\), this recovers the deterministic ODE exactly. For small \\(\sigma\_{t}\\), it approximately matches the original flow marginals (the noise coefficient differs by \\(O(\sigma\_{t}^{4})\\)). Crucially, this formulation has *exact* variance preservation, while Flow-GRPO's SDE inflates marginal variance. The cumulative effect of that inflation is the noisy intermediate samples we observed.

![Qualitative comparison of intermediate samples. Flow-GRPO's SDE produces visibly noisy images, while our DDIM-inspired SDE produces clean images while still injecting enough stochasticity for policy gradients.](./figure8-improved-sde.png)

**Figure 3.** Flow-GRPO's SDE produces visibly noisy intermediate samples (middle column). Our DDIM-inspired SDE (right column) produces clean images while still injecting enough stochasticity for policy gradients.

We use a noise schedule \\(\sigma\_{t} = \eta(t-\Delta t) \sqrt{1-t}\\). The schedule reduces exploration near the clean-image endpoint, and (via a tangent-flow analysis) compensates for the higher influence of early-step perturbations on the final image. Empirically, this makes the per-step exploration budget roughly uniform across the trajectory.

The two contributions, stepwise credit assignment and the improved SDE, are *complementary*. Each helps on its own, and combining them does better than either alone.

## Experiments

We trained Stable Diffusion 3.5-Medium with both Flow-GRPO and Stepwise-Flow-GRPO on three reward models of varying complexity: [PickScore](https://arxiv.org/abs/2305.01569) (a lightweight CNN), [ImageReward](https://arxiv.org/abs/2304.05977) (a medium transformer), and [UnifiedReward-7B](https://arxiv.org/abs/2503.05236) (a 7B-parameter VLM). Across all three, on both the [GenEval](https://arxiv.org/abs/2310.11513) compositional benchmark and the PickScore prompt set, Stepwise-Flow-GRPO converges faster per training iteration. Despite the per-iteration overhead of computing Tweedie estimates, it also converges faster in wall-clock time.

![Reward versus training step for Stepwise-Flow-GRPO and Flow-GRPO across four settings: PickScore on GenEval, ImageReward on GenEval, UnifiedReward on GenEval, and PickScore on the PickScore dataset.](./figure4-sample-efficiency.png)

**Figure 4.** Reward versus training step for Stepwise-Flow-GRPO (blue) and Flow-GRPO (red) across four settings. Stepwise-Flow-GRPO dominates throughout training.

The headline result comes from extended training. With 400 GPU hours on GenEval rewards, Stepwise-Flow-GRPO reaches **0.87 on GenEval overall**. For context: the base SD3.5-Medium scores 0.63, Flow-GRPO with extended training scores 0.72, and GPT-4o scores 0.84. The performance gap *widens* with training, particularly on counting (0.89), spatial positioning (0.73), and attribute binding (0.80), exactly the categories that demand precise compositional decisions.

| Model                                | Overall  | Counting | Position | Attr. Binding |
|:-------------------------------------|:--------:|:--------:|:--------:|:-------------:|
| SD3.5-M (base)                       | 0.63     | 0.50     | 0.24     | 0.52          |
| Flow-GRPO (400 GPU hrs)              | 0.72     |   --     |   --     |   --          |
| GPT-4o                               | 0.84     | 0.85     | 0.75     | 0.61          |
| **Stepwise-Flow-GRPO (400 GPU hrs)** | **0.87** | **0.89** | 0.73     | **0.80**      |

A few qualitative wins worth highlighting:

**Stability on complex rewards.** When training with UnifiedReward (the 7B VLM), Flow-GRPO consistently diverged. Stepwise-Flow-GRPO trained stably throughout. This is not just an efficiency story. Stepwise credit assignment seems to provide real stability benefits when reward gradients are noisy, as they tend to be with large VLM-based rewards.

**OCR text rendering.** A particularly striking case: with a combined OCR + PickScore reward, Flow-GRPO diverges after about 500 steps, while Stepwise-Flow-GRPO continues improving for 2000+. Text rendering is hierarchical (letter shapes and spacing must be set early; sharpening happens late), so it is a natural stress test for credit assignment, and we see big gains here.

**Compositional improvements.** Across qualitative comparisons, our method shows consistent gains in spatial reasoning, attribute binding, and counting. Flow-GRPO will sometimes merge objects when prompted with "X and Y", or place objects in physically implausible configurations (a bus floating in the sky, for example). Stepwise-Flow-GRPO produces cleaner compositions.

We also explored several design alternatives, including an exponential-moving-average baseline, generalized advantage estimation (GAE) over gains, and an ODE-based progressive distillation variant. None beat the simple gain formulation. Sometimes the natural temporal structure of the problem is best preserved rather than modeled away.

## Discussion

Stepwise gains open up several directions worth exploring. The per-prompt variance of gains is itself a useful signal: prompts where gains vary wildly are likely "hard" examples and could drive curriculum learning. Adaptively weighting steps proportional to their gain variance could focus optimization on the high-information regions of the trajectory. Most ambitiously, gains give the model a way to detect bad intermediate states, which suggests the possibility of *self-correcting diffusion*, where the model learns to retry a poor decision rather than press on.

There is also a clean conceptual takeaway. In multi-step generative processes (diffusion, flow matching, autoregressive language models, planning), the step-level structure is not a nuisance to be averaged over. It is information we should be exploiting. Uniform credit assignment is a tempting default, but it leaves signal on the table. Whenever your generative process has temporal hierarchy, finer-grained credit assignment likely pays. Tweedie's formula is the trick that makes it cheap for diffusion and flow models. Analogous tricks may exist for other domains.

For more details, see the [paper](https://stepwiseflowgrpo.com), where we also cover ablations on the number of denoising substeps, normalization strategies, and a comparison to concurrent work that addresses the same problem from different angles.
