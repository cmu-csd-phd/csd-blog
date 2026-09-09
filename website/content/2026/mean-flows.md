+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "Mean Flows for One-step Generative Modeling"
# Date must be written in YYYY-MM-DD format. Update to the date of the LAST committee approval signature before the final PR.
date = 2026-09-03

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Artificial Intelligence"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
tags = ["generative models", "diffusion models", "flow matching", "one-step generation", "image generation"]

[extra]
author = {name = "Zhengyang Geng", url = "https://gsunshine.github.io/" }
committee = [
    {name = "Tai-Sing Lee", url = "https://www.cnbc.cmu.edu/~tai/"},
    {name = "Christos Faloutsos", url = "https://www.cs.cmu.edu/~christos/"},
    {name = "Yonghao Zhuang", url = "https://zyhowell.github.io/"}
]
+++

Ask a modern image generator for a picture of an arctic fox, and behind the scenes it will start from pure random noise and repeatedly nudge that noise toward an image — often running a large neural network 50, 100, or even 250 times in sequence before a single picture emerges. This iterative refinement is what makes today's diffusion and flow models so powerful, and also what makes them slow and expensive to sample from.

This raises a tempting question: could a model instead jump from noise to a finished image in a *single* network evaluation, trained from scratch, with no distillation and no bag of tricks? This post is about [our NeurIPS 2025 oral paper](https://arxiv.org/abs/2505.13447) of the same name, where we show the answer is yes, and that the path to it runs through one small identity from freshman calculus.

![Five photorealistic images generated one-shot by a MeanFlow model: a sea anemone, a sleeping arctic fox, a stone monument, a lionfish, and a conch shell on sand.](./teaser-samples.png)

**Figure 1.** Class-conditional samples on ImageNet 256×256, each produced with a **single** function evaluation of a MeanFlow model trained from scratch.

## TL;DR

- **Problem.** Diffusion and flow models are slow to sample because they model *instantaneous velocity* — a field that only tells you which direction to step next. Generating a sample means numerically integrating that field along a curved trajectory, which takes many sequential network evaluations.
- **Idea.** Model the **average velocity** over a whole time interval instead of the instantaneous velocity at a point. If you know the average velocity, you can cross the entire interval in one jump: \\( z\_r = z\_t - (t-r) u(z\_t, r, t) \\). One-step generation is then just \\( z\_0 = z\_1 - u(z\_1, 0, 1) \\).
- **The MeanFlow Identity.** Average velocity is defined by an integral we cannot compute during training. Differentiating its definition converts that intractable integral into a *local* identity that the true field must satisfy: \\( u = v - (t-r)\frac{d}{dt}u \\). Integration becomes differentiation.
- **Training.** The identity turns directly into a regression loss whose only ground-truth signal is the ordinary flow-matching velocity. It costs one extra backward pass (a Jacobian-vector product), needs no curriculum or distillation, and reduces *exactly* to Flow Matching when the interval shrinks to a point.
- **Result.** An FID of **3.43** (lower is better) with a **single** network evaluation on ImageNet 256×256, trained from scratch — a 50–70% relative improvement over the previous best from-scratch one-step models, substantially narrowing the gap to multi-step generators.

## The cost of generating one image

At its heart, generative modeling is about transportation: we want to move a simple *prior* distribution we can sample from (say, Gaussian noise) onto the complicated *data* distribution we care about (say, natural images). [Flow Matching](https://arxiv.org/abs/2210.02747) is a clean and now-dominant way to set this up, closely related to diffusion models.

Pick a data point \\( x \\) and a noise sample \\( \epsilon \\), and connect them with a straight-line path indexed by time \\( t \in [0,1] \\):

\\[ z\_t = (1-t) x + t \epsilon. \\]

At \\( t=0 \\) we sit on the data, at \\( t=1 \\) on the noise. Differentiating gives the **velocity** of a point moving along this path, \\( v\_t = \epsilon - x \\): it is the arrow that says *which way, and how fast* to move at time \\( t \\). A neural network \\( v\_\theta(z\_t, t) \\) is trained to predict this velocity (more precisely, as we will see in a moment, its expectation), and once trained, we generate a sample by reversing the process — starting from noise at \\( t=1 \\) and following the arrows back down to data at \\( t=0 \\).

"Following the arrows" is the catch. The velocity field only tells us the *instantaneous* direction of motion, so recovering the actual endpoint requires solving an ordinary differential equation (ODE),

\\[ \frac{d}{dt} z\_t = v(z\_t, t), \\]

whose solution is an integral, \\( z\_r = z\_t - \int\_r^t v(z\_\tau, \tau)  d\tau \\). That integral has no closed form, so in practice we chop \\([0,1]\\) into many small time steps and take a little Euler step at each one, evaluating the network every time. More steps mean a more faithful integral — and more compute.

You might hope that with straight-line training paths, the trajectory we integrate would also be straight, letting us take one giant step. It is not. The subtlety is that a single point \\( z\_t \\) lies on the paths of *many* different (data, noise) pairs at once, so the network learns the **average** — the *marginal* velocity — over all of them:

\\[ v(z\_t, t) \triangleq \mathbb{E}\big[  v\_t \mid z\_t  \big]. \\]

Averaging bends things. Even though each individual training path is straight, the marginal field that actually governs sampling curves through space (Figure 2, right). And a curved trajectory traversed in a few coarse steps accumulates error — which is exactly why high-quality diffusion and flow sampling has needed many network evaluations.

![Left: several straight conditional flow paths, each with its own velocity arrow, passing through a shared point. Right: the marginal velocity field obtained by averaging them, whose trajectories are visibly curved.](./flow-matching-velocities.png)

**Figure 2.** Velocity fields in Flow Matching. **Left:** the *conditional* flows are straight, but a given point \\( z\_t \\) can be reached from many different (data, noise) pairs, each with its own velocity. **Right:** the *marginal* field the network actually learns averages over all of them, and its trajectories curve. Coarse discretization of a curved trajectory is what forces multi-step sampling. (Gray dots: prior samples; red dots: data samples.)

## What if we predicted the average velocity?

Here is the shift in perspective at the core of MeanFlow. The problem with instantaneous velocity is that it is a *local* quantity — it describes an infinitesimal moment, so stitching a full trajectory out of it requires integration. What if the network instead predicted a *global* quantity: the **average velocity** over an entire interval \\([r, t]\\)?

Define the average velocity \\( u \\) as total displacement divided by elapsed time,

\\[ u(z\_t, r, t) \triangleq \frac{1}{t-r} \int\_{r}^{t} v(z\_\tau, \tau)  d\tau. \\]

The payoff is immediate. Instantaneous velocity points along the *tangent* of the trajectory; average velocity is aligned with the *chord* — the straight line connecting where you are to where you want to be (Figure 3, left). Rearranging the definition, crossing the whole interval becomes a single subtraction:

\\[ z\_r = z\_t - (t-r) u(z\_t, r, t), \\]

and one-step generation from noise is just \\( z\_0 = z\_1 - u(z\_1, 0, 1) \\): sample noise, evaluate the network once, and you are done. No integral, no trajectory, no sequential steps.

![Left: a curved path with the tangent instantaneous velocity v and the chord-aligned average velocity u drawn at a point. Right three panels: the average-velocity field for target times t = 0.5, 0.7, and 1.0, arrows fanning out along the chords to the endpoint.](./average-velocity-field.png)

**Figure 3.** The field of *average velocity* \\( u(z, r, t) \\). **Left:** while the instantaneous velocity \\( v \\) is tangent to the path, \\( u \\) is aligned with the *displacement* \\( (t-r) u \\) — the chord. **Right:** unlike \\( v \\), the field \\( u \\) depends on *two* times, a start \\( r \\) and an end \\( t \\); three slices are shown.

Two things are worth emphasizing. First, \\( u \\) is not a new modeling assumption or a network trick — it is a perfectly well-defined field *induced* by the instantaneous velocity \\( v \\), a functional of it, existing whether or not any network is around. That means it is a genuine ground-truth target we can aim at, just as \\( v \\) is the ground truth in Flow Matching. Second, this field comes with structure for free: as the interval shrinks (\\( r \to t \\)) the average returns to the instantaneous velocity, \\( u \to v \\); and splitting an interval is automatically self-consistent, since the displacement over \\([r,t]\\) is the sum of the displacements over \\([r,s]\\) and \\([s,t]\\). A network that truly matches \\( u \\) inherits this consistency without our having to impose it.

There is, of course, a catch — the one that makes this more than wishful thinking. The definition of \\( u \\) contains the very integral we were trying to avoid. Using it directly as a training target would mean computing an integral for every sample, every step. We need a way to pin down \\( u \\) that never asks us to integrate.

## The MeanFlow Identity

This is where a single line of calculus does all the work. Clear the fraction in the definition to expose the integral,

\\[ (t-r) u(z\_t, r, t) = \int\_{r}^{t} v(z\_\tau, \tau)  d\tau, \\]

and differentiate both sides with respect to the end time \\( t \\), holding the start time \\( r \\) fixed. The left side is a product rule; the right side is the Fundamental Theorem of Calculus, which simply hands us back the integrand \\( v(z\_t, t) \\). Rearranging the result gives what we call the **MeanFlow Identity**:

\\[ \underbrace{u(z\_t, r, t)}\_{\text{average velocity}} = \underbrace{v(z\_t, t)}\_{\text{instantaneous velocity}} - (t-r)\underbrace{\frac{d}{dt} u(z\_t, r, t)}\_{\text{time derivative}}. \\]

Look at what happened. The definition of \\( u \\) was a *global*, intractable statement — an integral over a whole interval. The identity is an equivalent *local* statement: a relationship between \\( u \\), the ordinary velocity \\( v \\), and \\( u \\)'s own rate of change, all evaluated at a single point. We have traded an integral we cannot compute for a derivative we can. A slogan from our NeurIPS poster captures the spirit:

> Integration is generation; differentiation is verification.

The slogan is only half a joke. *Generating* a sample means integrating the field along an entire trajectory — expensive, and the very thing we are trying to escape. But *verifying* that a candidate field is the true average velocity only requires differentiating it at individual points and checking the identity. Training, as we will see next, only ever needs verification.

The one remaining piece is that total time derivative \\( \frac{d}{dt} u \\). Because \\( z\_t \\) itself moves with time, the chain rule expands it into

\\[ \frac{d}{dt} u(z\_t, r, t) = v(z\_t, t) \partial\_z u + \partial\_t u, \\]

where \\( r \\) contributes nothing since we hold it fixed. This is precisely a **Jacobian-vector product (JVP)**: the derivative of \\( u \\) contracted against the tangent direction \\( (v, 0, 1) \\). Modern autodiff frameworks compute JVPs directly and cheaply — `torch.func.jvp` in PyTorch, `jax.jvp` in JAX — in roughly the cost of one extra backward pass. The intractable integral has become a one-line autodiff call.

## Training a MeanFlow model

Everything above is about the true fields and holds for any network. To learn, we parameterize the average velocity with a network \\( u\_\theta(z\_t, r, t) \\) and ask it to satisfy the MeanFlow Identity. That is a regression problem: match the network's output to the right-hand side of the identity, used as a target.

\\[ \mathcal{L}(\theta) = \mathbb{E} \big\Vert u\_\theta(z\_t, r, t) - \operatorname{sg}(u\_{\text{tgt}}) \big\Vert\_2^2, \\]
\\[ u\_{\text{tgt}} = v\_t - (t-r)\big( v\_t \partial\_z u\_\theta + \partial\_t u\_\theta \big). \\]

A few things make this practical and, we think, elegant:

- **The only ground-truth signal is the flow-matching velocity** \\( v\_t = \epsilon - x \\), the same cheap target used everywhere in Flow Matching. We never touch the integral. The derivative term in the target is supplied by the network's own JVP.
- **Stop-gradient** (\\( \operatorname{sg} \\)) is applied to the target. This keeps the JVP a constant as far as the parameter update is concerned, so we avoid differentiating through a derivative — no expensive higher-order gradients. In our JAX implementation the JVP adds under 20% to training time.
- **MeanFlow contains Flow Matching.** If we restrict the interval to a single point, \\( r = t \\), the correction term \\( (t-r)(\cdots) \\) vanishes and the loss becomes ordinary Flow Matching. The whole method is Flow Matching plus one extra term — the term that, precisely, buys one-step sampling. In training we simply sample \\( (r, t) \\) pairs, sometimes with \\( r = t \\), and let the identity do the rest.

It is worth contrasting this with prior work on one-step generation. The [Consistency Models](https://arxiv.org/abs/2303.01469) family *imposes* a consistency constraint on the network's behavior — a property we wish the network had — and getting it to train well requires a carefully tuned "discretization curriculum" that gradually anneals the time grid; in our notation, these models also fix the jump target at \\( r = 0 \\), so the network is conditioned on a single time. More recent two-time methods — [Shortcut models](https://arxiv.org/abs/2410.12557) and [Inductive Moment Matching](https://arxiv.org/abs/2503.07565) — condition on an interval as we do, but they too add extra self-consistency constraints between time scales. MeanFlow needs none of that. The identity we train against is not a heuristic we hope holds; it is forced by the definition of average velocity itself. The ground-truth target exists independently of the network, which is what makes training stable and self-contained.

One more benefit falls out naturally: **classifier-free guidance (CFG)**, the standard lever for trading diversity against fidelity, usually doubles sampling cost because it evaluates the network twice. We instead fold guidance into the ground-truth field itself, so the guided average velocity is again something the network models directly — preserving true single-evaluation sampling even with guidance on.

## Does it work?

Yes, and by a clear margin. Two pieces of vocabulary first. Generation quality is measured by **FID** (Fréchet Inception Distance), which compares the distribution of generated images against real ones — lower is better, and the strongest many-step models on ImageNet 256×256 sit around 2. Sampling cost is counted in **NFE**, the number of function evaluations: how many times the network must be run to produce one image.

On this benchmark, a MeanFlow-XL model (676M parameters) trained **from scratch** reaches an **FID of 3.43 at 1-NFE**. The prior from-scratch one-step models of the same size were far behind: Shortcut-XL at 10.60 and iCT-XL at 34.24, while IMM-XL's best "one-step" result — which uses guidance and therefore actually costs 2 NFEs — was 7.77. Against the strongest of these, MeanFlow improves FID by 50–70% in relative terms, and it does so without any of the usual crutches: no pre-training, no distillation from a slow teacher, no curriculum.

![A bubble chart of one-step FID versus training compute on a log scale. Four MeanFlow models form a low frontier running from FID 6.17 down to 3.43, far below iCT-XL at 34.24, Shortcut-XL at 10.60, and IMM-XL at 7.77.](./fid-vs-gflops.png)

**Figure 4.** One-step generation on ImageNet 256×256: FID versus *training* compute (log scale; bubble area indicates model size). Every MeanFlow variant, from MF-B to MF-XL, sits well below the prior one-step models — iCT-XL (34.24), Shortcut-XL (10.60), and IMM-XL (7.77, whose one-step sampling uses guidance and thus 2 NFEs) — at comparable or lower training cost.

The approach is also well-behaved as we scale it up. Across model sizes from 131M to 676M parameters and training runs from 40 to 240 epochs, one-step quality improves smoothly along both axes (Figure 5) — the gains are not a small-scale artifact but a property of the formulation.

![Line chart of one-step FID versus training epochs for four MeanFlow model sizes. Every curve decreases steadily, larger models are uniformly better, and the four curves end at FID 6.17, 5.01, 3.84, and 3.43.](./scalability.png)

**Figure 5.** Scaling behavior. 1-NFE FID versus training epochs for four MeanFlow sizes (B/2 to XL/2). Bigger models and longer training both help, monotonically — while sampling stays a single network evaluation.

An honest accounting of where things stand: the strongest many-step systems still hold an edge. DiT-XL and SiT-XL reach FIDs of 2.27 and 2.06 — but they spend 250 sampling steps per image, doubled to 500 network evaluations once guidance is on. One-step generation has not erased that gap; it has changed its scale. What used to be a 5× difference in FID between from-scratch one-step models and their many-step counterparts is now a gap of about one point — and granting MeanFlow just a second evaluation (2-NFE, with longer training) brings it to 2.20, within touching distance of models that spend two orders of magnitude more compute per image.

## Why this matters

Step back from the images and the FID numbers, and the takeaway is methodological. The dominant recipe for fast generation had been to *constrain a network's behavior* — tell it to be self-consistent across steps — and then engineer the training procedure until that constraint could be satisfied. MeanFlow suggests a different discipline: first identify the true mathematical object you want (here, the average velocity), then derive the exact identity that object must obey, and only then attach a network and regress toward it. When the target is a real, network-independent field, you often need far fewer heuristics to hit it.

There is also a nice piece of accounting hidden in the story. Flow and diffusion models pay for sampling at *inference* time, integrating a velocity field step by step, over and over, for every image they ever generate. MeanFlow moves that cost to *training* time: the JVP in the loss is a one-time price paid while learning, in exchange for turning every future generation into a single subtraction. Integration at inference becomes differentiation at training — the Fundamental Theorem of Calculus, put to work as a systems trade-off.

Cheap sampling is not only a convenience; it changes what these models can do. A generator that needs one evaluation per image can run at interactive latency, sit inside a larger system that calls it in an inner loop, and — because the same network models *every* interval \\([r, t]\\) — trade a second or third evaluation for extra quality at deployment time, with no retraining.

We hope MeanFlow encourages people to revisit the foundations of these models rather than to keep bolting heuristics onto them. If you would like to try it or read the details, the paper is [_Mean Flows for One-step Generative Modeling_](https://arxiv.org/abs/2505.13447), and the code is available at [github.com/Gsunshine/meanflow](https://github.com/Gsunshine/meanflow).
