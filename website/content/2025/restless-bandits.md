+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "Restless bandits"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2025-04-29

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Theory"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
# Consider these similar to keywords specified for a research paper.
tags = ["restless bandits", "long-run average reward", "asymptotic optimality"]

[extra]
author = {name = "Yige Hong", url = "https://www.cs.cmu.edu/~yigeh/" }
# The committee specification is  a list of objects similar to the author.
committee = [
    {name = "Committee Member 1's Full Name", url = "Committee Member 1's page"},
    {name = "Committee Member 2's Full Name", url = "Committee Member 2's page"},
    {name = "Committee Member 3's Full Name", url = "Committee Member 3's page"}
]
+++

Restless bandit problem is a stochastic decision problem where the decision maker dynamically allocates resources among a set of "arms" to maximize the reward in the long term.  
It is a suitable model for many "weakly-coupled" decision problems, with applications ranging from scheduling, communication, online advertising, machine maintenance, etc. 
Despite its importance, the restless bandit problem is notoriously hard in theory --- even an approximate notion of optimality can only be achieved under restrictive assumptions. 

In this blog, we informally introduce some recent progress that relaxes the conditions for achieving _asymptotic optimality_ in restless bandits, based on our paper _[Unichain and aperiodicity are sufficient for asymptotic optimality of average-reward restless bandits](https://arxiv.org/abs/2402.05689)_. 
We will also briefly mention a generalization of the result to heterogeneous arms, multi-action and general cost functions, covered in the followup paper _[ID policy (with reassignment) is asymptotically optimal for heterogeneous weakly-coupled MDPs](https://www.arxiv.org/abs/2502.06072)_. 

The blog will be organized as follows: we first set up a simple example to introduce the problem and provide intuitions for our control policy. Then we provide the pseudo-code of the policy, state the theorem, and provide a proof sketch. Finally, we will briefly discuss the generalization of our result. 


<!-- 
# Overview
Dynamic decision probelm called restless bandits, which is, roughly speaking, controlling a large number of Markov Decision Processes under resource constraints

This is a classic **theoretical** problem with a long history and wide applications (list a few) (cite papers). 
Optimality is in general intractable, the goal is ``asymptotic optimality''. Still need restrictive conditions. 

We will introduce a policy called "ID policy" that is asymptotically optimal under a very weak condition. 

We first introduce RB via a made-up example. Then build towards our policy. Then a present a theoretical result and informal proof sketch. 

Finally, a bit of generalizations -->


# Flappy bird challenge for octopus
A gamer in the octopus world, Sakiko, wants to challenge a world record --- playing the largest number of _Fappy Bird_ at the same time. Flappy Bird is a game where a bird flies through a forest of pipes; the player controls a bird to fly up and down to avoid the pipes. 

<figure style="text-align: center;">
<img src="../../static/2025/restless-bandits/flappy-bird.png" alt="MDP" style="max-height: 40vh; width: auto;"/>
 <figcaption style="margin-top: 0.5em;"> <b>Figure 1</b>: Flappy Bird </figcaption>
</figure>


Flappy bird is challenging game for most humans, but not for Sakiko, who is a genius octopus gamer --- when played with attention, she can play Flappy Bird forever without making any mistakes. Moreover, she can play multiple games at a time with her flexible tentacles. 

However, even an octopus has a finite number of tentacles, and Sakiko can play at most 80 games at the same time without degrading the performance. 
Fortunately, the organizer allows Sakiko to use bots for assistance. 
A bot can play the game at a coarse granuity: 
in the easy episodes, a bot achieves 100% success rate; in the difficult episodes, a bot only has 10% success rate of passing each pipe. 
The organizer gives Sakiko the access to an unlimited number of bots. 


<figure style="text-align: center;">
<img src="../../static/2025/restless-bandits/my_sakiko.png" alt="Sakiko" style="max-height: 30vh; width: auto;"/> 
 <figcaption style="margin-top: 0.5em;"> <b>Figure 2</b>: Sakiko </figcaption>
</figure>



The specific rule is as follows: 
- Sakiko opens Flappy bird on $N$ smartphones and start them simultaneously. Then at each moment, she can choose to operate on a subset of the games, and leave the rest to the bots. 
- When Sakiko reaches the end of an episode of each game, she score $1$ point, and goes to the next episode; when she fails, the game restarts from the initial episode. 
- Some episodes are difficult and require Sakiko's interference, while some episodes are easy and can be left to the bots without incurring a mistake; these two types of episodes interleave randomly. 
- The goal is to maximize the total score averaged over a long enough period of time. 


<!-- (this part: make sure the game rule is super clear, but no need to map it to the structure of MDPs)
(next section, connect the problem to an MDP, and state the MDP's definition) -->


# Model
<!-- We consider the games as changing at discrete times. 

There are $N$ games. Every time step, Sakiko chooses a fixed fraction of games to play, and leave the rest to bots.  -->

<!-- We first define each game as an MDP, and the define the whole problem as a restless bandit problem. -->

(to do: each game? MDP? subproblem? arm?) 

### Model each game as a Markov Decision Process

(An important possible confusion: each state is a pipe, or an episode? There are two episodes? infinitely many episode? Maybe use colors on the states to clarify, or explicitly draw the mapping... )

We consider the games as changing at discrete times. 
Each game has a state, i.e., which episodes the bird is in and how long long until the episode ends. 
Based on the state of the game, Sakiko can choose to interfere, or not interfere --- which means let a bot operate for this time step. 
The decisions leads to differet immediate and future consequences. 

To analyze in detail the consequence of different decisions, 
we model each game as a Markov Markov Decision Process (MDP). 
An MDP is defined by four elements: _state space_, _action space_, _transition probabilities_, and _reward function_. In this example, 
- State space $\mathbb{S} = \{1,2,\dots k, k+1, \dots k+m\}$, where the first $k$ states correspond to pipes in a difficult episode, and the last $m$ states correspond to pipes in an easy episode. 
- Action space $\mathbb{A} =\{0,1\}$, where action $1$ means to interfere, and action $0$ means to not interfere. 
- The state transitions randomly, and the distribution of the next state depends on the current state and action. 
- The reward is also a function of the current state and action. 


Decription of state transition (illustrated by [Figure 3](#fig:mdp)):
- Each time, success or fail. The success prob. depends on whether it is a hard or easy episode ($s\leq k$ or $s > k$) and whether Sakiko interferes. 
- If success in the middle of an episode, move forward. 
- If success in the at the end of the episode, jump to state $1$ (the beginning of the difficult episode) or the state $k+1$ (the beginning of the easy episode) with equal probabilities, and get $1$ unit of reward; if fail start over from state $1$ (in a difficult episode). 


<figure id="fig:mdp" style="text-align: center;">
<img src="../../static/2025/restless-bandits/mdp.png" alt="MDP"  style="max-height: 35vh; width: auto;"/>
    <figcaption style="margin-top: 0.5em;"> <b>Figure 3</b>: Illustration of the MDP.  Cycles denote the states, and arrows denote possible transitions. A black arrow corresponds to a success event within an epside, a green arrow corresponds to a success event at the end of an episode, and a red arrow corresponds to a failure event. 
</figcaption>
</figure>

More precisely, the transition probabilities and the reward function can be represented in the form of the transition kernel $(P(s,a,s'))_{s,s'\in\mathbb{S}, a\in\mathbb{A}}$ and reward function $(r(s,a))_{s\in\mathbb{S},a\in\mathbb{A}}$, 
where $P(s,a,s')$ denotes the probability of going to state $s'$ in the next time step, when takes action $a$ at state $s$, and $r(s,a)$ denotes the reward of taking action $a$ at state $s$. 
Here we omit writing them out the transition in full for concreteness; instead, we specify them in the pseudo-code. 
```python
import numpy as np

def get_next_state_and_reward(s,a):
    # If in an easy episode or being interfered
    if (s >= k+1) or (a == 1):
        p_succ = 1
    # If in a hard episode or being interfered
    else:
        p_succ = 0.1
    p_fail = 1 - p_succ

    if (s < k) or (k+1 <= s < k+m): 
        # in the middle of an episode
        success = np.random.binomial(n=1, p=p_succ)
        next_state = s+1 if success else 1
        reward = 0
    else: 
        # at the end of an episode
        go_to_1 = np.random.binomial(n=1, p=p)
        next_state = 1 if go_to_1 else k+1
        reward = p_succ
    return next_state, reward
```



### Multiple games as restless bandits


<figure id="fig:rb" style="text-align: center;">
<img src="../../static/2025/restless-bandits/rb.png" alt="RB"  style="max-height: 40vh; width: auto;"/>
    <figcaption style="margin-top: 0.5em;"> <b>Figure 4</b>: Illustration of the restless bandits. 
</figcaption>
</figure>

Suppose there are a set of $N$ games, and Sakiko can interfere with $\alpha N$ of them at the same time. 

We assume $\alpha = k/(k+m)$ for simplicity. 

The goal is to maximize the long-run average reward in an infinitely long time horizon. 

Lots of MDPs, want asymptotic optimality


<!-- ```
$1\leq s < k$ or $k+1\leq s < k+m$:  
- Jump from $s$ to $s+1$ or fall back to $1$, with prob. success or fail

$s=k$ or $s=k+m$:
- Jump to $1$ with prob. fail or success/2; reward p success
- Jump to $k+1$ with prob. success/2.

Success prob is $1$ if $a = 1 \text{ or } s<=k$ ; $0.1$ otherwise
``` -->






State both the formal definition, and the specific chain structure
- Each drone is a Markov Decision Process: two types of transitions depending on the actions
    - Drone problem: a picture of the MDP
    - Special setting: the first minute requires human control
- Hard budget constraint every time step
    - Special setting: play $\alpha = k/(k+m)$ fraction
- Maximize reward
- Lots of MDPs, want asymptotic optimality


<!-- (This is a bit non-intuitive; try to write this in a slightly more compact form.)
(not fully correct, $P(i,1,a)$ is special...?)
($r(s,a)=0$, $P(s,a,s')=0$ by default; use $s$ instead of $i$)


For $i\leq k-1$ or $k+1 \leq i \leq k+m-1$: 
$$
P(i,a,i+1) = 
\begin{cases}
    1 &\text{ if } a = 1 \text{ or } i<k \\
    0.1 &\text{ if } a = 0 \text{ and } i\geq k.
\end{cases}
$$

For $i\in \{k, k+m\}$:
$$
P(i,a,1) = P(i,k+1,a) = 
\begin{cases}
    0.5 &\text{ if } a = 1 \text{ or } i<k \\
    0.05 &\text{ if } a = 0 \text{ and } i\geq k.
\end{cases}
$$
and 
$$
r(i,a) = 
\begin{cases}
    1 &\text{ if } a = 1 \text{ or } i<k \\
    0.1 &\text{ if } a = 0 \text{ and } i\geq k.
\end{cases}
$$


For any $i$, 
$$
P(i,a,1) = 
\begin{cases}
    0 &\text{ if } a = 1 \text{ or } i<k \\
    0.9 &\text{ if } a = 0 \text{ and } i\geq k.
\end{cases}
$$ -->




# Policy
Q: How to approach this problem?

A: Product space, a big MDP ... intractable.

Q: What can we learn from controlling a single-arm?

A: Optimal single-armed policy, defined as...
On this instance, single-armed policy is ... Always success, 
This policy induces a Markov chain, uniform distribution as steady state. ... 

Intuitively, the optimal single-armed policy tells us the most ``operation efficient'' way of controlling the MDP. In this example, we want to interfere only when necessary. 

If we could strictly follow the optimal single-armed poilcy, then we are good. This is indeed possible if ... 

but the constraints forces us to choose, to do the tie-breaking on ``equally efficient states''

Q: How to do the tie-breaking?

A naive idea is random tie-breaking policy: 
randomly select a drone that requires operations

Q: Does it work?

No. 

<img src="../../static/2025/restless-bandits/RandomTBAnimation-flappy-4-21-0.1-N-500-T-300-init-bad.gif" alt="Random Tie-breaking" style="max-height: 40vh; width: auto;"/>

Q: Why? 
Short ansewr: lack of persistency. (explain the movements)


Q: What is another natural idea?

A: tracking the ID is crucial; then we break ties in the fixed order. 
Specifically, ... (explain the movements)

<img src="../../static/2025/restless-bandits/IDAnimation-flappy-4-21-0.1-N-500-T-300-init-bad.gif" alt="ID policy" style="max-height: 40vh; width: auto;"/>


Remark: [add a box]

In practice, more sophisticated tie-breakings are used (cite);
mainly index policies, prioritize some states over others.
They have their own merit, with nice properties in certain situations; 
they work well in practice, and are widely applied. 

However, fundamentally, lack of optimality guarantees under general conditions. 
They require the assumption ``global attractor property'': mean-field limit is non-linear and different from Markov chain...
we refer to ... for detailed definitions ...  

Fundamental reason: lack of persistency. (Some nice images and examples in my FTVA and ID poilcy papers). 

Intuitively, MDP, achieve some goal, need persistent efforts; state-based ``greedy'' priority policies do not track this. 


# ID policy and results

ID policy definition (using the example)
- We call it "ID policy" as opposed to "index policy".
- Introduce the LP, solve the optimal single-armed policy
- Formal pseudo-code

Assumption: Markov chain mixing

(formal details: finite-state, reward $\in[0,1]$)

Theorem: asymptotic optimality 
<!-- $$
    R^{rel} - R(\pi, \bm{S}_0) \leq \frac{672\lambda_W^{5/2}|\mathbb{S}|^{3/2}}{\min(\alpha,1-\alpha)^3\sqrt{N}}.
$$ -->
$$
    R^{rel} - R(\pi, \bm{S}_0) = O\left(\frac{\tau^4}{\sqrt{N}}\right)
$$
where $\tau$ is the mixing time of the total variation distance. 


# Analysis sketch

Focus set

Mixing, and expansion of the focus set. 

Mention "Lyapunov functions" (skip the details.)

Try to intuitively explain the 4-th order dependency on $\tau$

# Generalizations
we can also do multiple actions, cost functions, heterogeneous arms, etc.; naturally generalize

see this paper ...
