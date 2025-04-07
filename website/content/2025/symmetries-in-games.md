+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "Leveraging Symmetries in Strategic Games"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2025-08-13

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Artificial Intelligence", "Theory"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
# Consider these similar to keywords specified for a research paper.
tags = ["Game Theory", "Nash Equilibrium", "Symmetries", "Computational Complexity", "Algorithms"]

[extra]
author = {name = "Emanuel Tewolde", url = "https://emanueltewolde.com/" }
# The committee specification is  a list of objects similar to the author.
committee = [
    {name = "Nihar Shah", url = "https://www.cs.cmu.edu/~nihars/"},
    {name = "Steven Wu", url = "https://zstevenwu.com/"},
    {name = "Carlos Martin", url = "https://www.linkedin.com/in/carlosgmartin/"}
]
+++

_The content of this blog post is derived from the research paper [Computing Game Symmetries and Equilibria That Respect Them](https://emanueltewolde.com/files/symmetries.pdf) published at AAAI-25. It is authored by Emanuel Tewolde, Brian Hu Zhang, Caspar Oesterheld, Tuomas Sandholm, and Vincent Conitzer._

_TL;DR: We study the implications of symmetries in strategic games. Using the classical framework of normal-form games, we investigate how hard it is to Nash equilibria that respect a set of symmetries, and in what cases we can leverage symmetries to get efficient algorithms. In general games and games with common payoffs, we show PPAD- and CLS-completeness, that is, these problems are exactly as hard as Brouwer fixed point and gradient descent problems. In games with a vast number of symmetries or in two-player zero-sum games, on the other hand, we manage to devise polynomial-time algorithms._

# 1. Let's play a game!
<p align="center">
<img src="./coloredlevers.png" alt="A two-player coordination game. If both players pick the same color out of four (red, yellow, blue, green), they each receive the associated utility points, which are 10, 12, 12, and 12. If they miscoordinate, both receive 0 points. Without knowing who you are playing with, what color would you choose?" width="300">
</p>
You and I shall choose one of the four colors red, yellow, blue, green (henceforth, also, R,Y,B,G) in the image above. If both of us pick the same color, we each receive the points associated to the color. If we miscoordinate, we each receive 0 points. We cannot communicate, and even further, say we do not know each other or whether the partner is even human or an AI agent. Which color would you pick in order to maximize your points? Please give yourself 10 seconds to think about your choice.

## Coordination Issues
It is not totally clear how to play the game well. In an ideal scenario, we would manage to coordinate on the same color between the three that yield the maximal 12 points (Y,B,G). But the three colors are _symmetric_ to each other (in a sense made precise further down), so which one do you pick? If we previously played the game together and succeeded in coordinating, this might give us a strong inclination to simply repeat that color. In this blog post, however, we will focus on the situation where we are interacting with a novel partner. In real-world applications, this might be, for instance, because we are playing a game of pick-up soccer, or entered a new business partnership.

Even then, we might hope to apply conventions; think of driving on the right (or left) side of the road. I, for example, was inclined to play the color on the _opposite side_ of the distuingishable color red, which is green. Alternatively, we might resort to a so-called _focal point_, which is an option that another agent might choose at default. For many humans, that might be the blue color since it is the most frequent favorite color in the world. But then again, how do you know that the agent on the other side has the same conventions or focal points in mind when taking their decision?

We argue it is not possible to predict consistently how a novel / unknown partner will break this symmetry. Therefore, it is reasonable to assume that if the partner decides to pick one of the three symmetric colors (Y,B,G), then from our perspective, they are just as likely to have picked any of the other two colors. Under that assumption, we can only expect to achieve an average of 4 points from picking one of the three symmetric colors ourselves. 
The points-maximizing strategy suddenly has now become to play the red color, which is a color that does not suffer from indistuingishable from other colors via symmetries.

In this blogpost we investigate how hard it is to compute Nash equilibria---the classical and most standard solution concept---that respect the symmetries of a game. In Section 2, we will find that the general problem has a comparable computational complexity as finding any Nash equilibrium of a game (symmetry-respecting or not). In Section 3, we will present two important special cases in which we can achieve efficient (polynomial-time) computability.

+++ If the other player recognizes the symmetry constraints themselves, they will face the same calculations: +++

+++ We argue it is not possible to break the symmetry in a consistent fashion across mutually novel agents +++

## Why we care about (respecting) symmetries
Symmetries are ubiqituos in game theory and multi-agent systems. For one, central concepts such as cooperation, conflict, and coordination are usually presented most simply on symmetric games, such as the Prisoner’s Dilemma, Chicken, and Stag Hunt. Classic algorithms for equilbrium computation, such as Lemke-Howson, are frequently (and without loss of generality) presented for symmetric games for the sake of clarity. Furthermore, interactions with symmetries oftentimes can be described more concisely in comparison to enumerating all individual outcomes and payoffs of a game: “Matching Pennies is a two-player game where each player picks a side of a coin {Heads, Tails}. If both players pick the same side, player 1 wins, otherwise, player 2 wins.” This is oftentimes leveraged in games where we design the outcome and reward structures, such as in social choice and mechanism design via anonymity, neutrality, and fairness axioms. Indeed, notions of fairness have been connected to the premise that any participant of the game might be assigned to any player identity in the game, which forms a symmetry across participants. For the sake of fairness, one would then like the player identities to be equally strong (_cf._ the Matching Pennies game, and the “veil of ignorance” philosophy by John Rawls [1971]). 

This symmetry idea that any participant (AIs, humans, etc.) might take on any player identity in the game (e.g., black versus white in chess) also reappears when reasoning about other agents of which we do not have a prior: since the beginnings of machine learning---in 1959, when **first** Samuel studied the game of checkers---, it has been popular to learn good strategies in _self-play_, that is, to assume that other players would use the same strategy as oneself. Self-play continues to be a core contributor to AIs that can learn with no or limited access to human data, and reach super-human performance in domains such as Go and poker with the AlphaGo series by Silver _et al._ [2016, 2017] and Libratus & Pluribis by Brown and Sandholm [2018, 2019]. Beyond leveraging the player symmetry in chess and Go by always orienting the board from the moving player’s perspective, Silver _et al._ also exploit the rotation and reflection symmetries in Go. Several other general-purpose game solvers achieve state-of-the-art performance, in part, by imposing symmetry invariances onto their neural network architecture (Marris et al. 2022, Liu et al. 2024)

We may also utilize game symmetries for the purposes of strategy pruning and equilibrium selection. We have already illustrated this in the previous subsection, where the symmetry constraints prune the strategies (Y,B,G) that may lead to 12 points because when playing them, the players run a significant risk of miscoordinating. If the game were to be repeated multiple times with the same partner, on the other hand, symmetry-based pruning will continue to keep strategies that achieve a long-term average of
12 points (we give an example **in this footnote^1**). These issues have received quite some research attention in recent years under the umbrella term _zero-shot coordination_ or _ad-hoc teamwork_.

Last but not least, some strategic interactions may also force symmetric play across different decision points. This could be, for instance, because multiple agents (say, self-driving cars) run the same software for taking decisions. In another example, an agent may not recall being in the same situation before (absentmindedness) because, _e.g._, the agent does not retain any record of its history. In this case, it will necessarily act in the same fashion as it did before. For **Theorem 8**, for instance, we make precise and exploit that there does not appear to be a sharp distinction between (1) being absentminded, (2) being multiple copies of the same agent, and (3) symmetric agents playing symmetries-respecting profiles.


+++ : 1. both playing red, 2. both playing yellow, blue, green with 1/3 probability each, and 3. an approximate mix between those two profiles (both playing 12/42 red, 10/42 yellow, 10/42 blue, 10/42 green). +++

+++ Moreover, many no-regret learners (_e.g._ gradient descent, regret matching, etc.) in self-play and under symmetric initializations continue to respect the symmetries in a game throughout the learning process. +++

# Symmetries-Respecting Equilibria

The results we discuss in this blogpost hold for arbitrary finite normal-form games: There is a finite number of players, a finite number of _actions_ per player, and each player has a _utility_ function specifying her utility from any tuple of actions chosen by all players. For the sake of exposition, however, we will stick to games with two players, in which each player has to choose one of \\(m \in \mathbb{N}\\) _actions_. Such games can be represented as a pair of two utility matrices \\(A,B \in \mathbb{R}^{m \times m}\\). The Matching Pennies game described previously is then a game with \\(m=2\\) actions represented as follows:
<p align="center">
<img src="./MP.png" alt="The Matching Pennies game." width="300">
</p>
Subscript '1' here corresponds to 'heads' in our previous language description, and subscript '2' corresponds to 'tails'. Player 1 (PL1) tries to match the action of PL2, and PL2 tries to mismatch the action of PL1. We will use this game as a running example.

## Game Symmetries
A narrow notion of symmetry _à la_ von Neumann and Morgenstern (1944), which we refer to as _total symmetry_, requires \\(A = B^T\\) for two-player games. That is, we can swap the player identities and the utility outcome for each player would remain the each player continued to play the "action number" they planned to play before the player swap.  As we can see, Matching Pennies is not totally symmetric. However, Matching Pennies does have a symmetry in the sense of map <span style="color: deepskyblue;">\\(\phi\\)</span> below:
<p align="center">
<img src="./MPsymm.png" alt="A symmetry of Matching Pennies." width="300">
</p>

This symmetry map not only swaps the player identities, but it also swaps the action numbering of PL1. With it, the PL1 as a matcher becomes a mismatcher in PL2. To be precise, applying <span style="color: deepskyblue;">\\(\phi\\)</span> indeed does not change the utility outcomes: We may, for example, check what PL1 receives under _action profile_ \\((a_1,b_2)\\), that is PL1 playing the first row and PL2 playing the second column. The <span style="color: deepskyblue;">\\(\phi\\)</span>-corresponding scenario then is to check for PL2's utility under \\((a_2,b_2)\\). In both scenarios, the respective players receive \\(-1\\) utility. In the same fashion, we can check that utilities remain unchanged upon applying <span style="color: deepskyblue;">\\(\phi\\)</span> under any scenario.

**Definiton** (Nash 1951): A game symmetry \\(\phi\\) specifies a bijective player map \\(\pi : \\{1,2\\} \to \\{1,2\\}\\) and bijective action maps \\(\phi_1,\phi_2 : \\{1,\dots,m\\} \to \\{1,\dots,m\\}\\) such that for any player \\(i \in \\{1,2\\}\\) and under any action profile \\((a,b) \in \\{1,\dots,m\\}^2\\), we have that player \\(i\\) receives exactly as much utility under \\((a,b)\\) as player \\(\pi(i)\\) receives under \\((\phi_1(a),\phi_2(b))\\).

Interestingly enough, the set of symmetries form an algebraic group, _i.e._, we can compose and invert symmetries to obtain further symmetries. For example, \\(\phi^2\\) in Matching Pennies is another interesting symmetry because here, PL1 as the matcher continues to match (\\(\pi(1) = 1\\)), but the labeling of the actions heads and tails get swapped for both players simultaneously.

## Respecting Symmetries
In game theory, we allow players are not only to play a single action, but to instead play a probability distribution \\(s_i\\) over their \\(m\\) actions, which we will henceforth call a (mixed) strategy. Given a _strategy profile_ \\(s = (s_1,s_2)\\) and a symmetry \\(\phi\\), we can then also consider the strategy profile \\(\phi(s)\\) that we get from applying \\(\phi\\) to \\(s\\).

**Example**: The strategy profiles \\( s \\) = \\((\\) (70% heads, 30% tails) , (20% heads, 80% tails) \\()\\) in Matching Pennies mapped under <span style="color: deepskyblue;">\\(\phi\\)</span> would result in the strategy profile \\( \phi(s) \\) = \\((\\) (20% heads,  80% tails) , (30% heads, 70% tails) \\()\\).

For the various reasons we have discussed in the introduction, we are interested in strategy profiles that _respect_ the symmetries of a game. 

**Definition**: A strategy profile \\( s \\) in a game respects a symmetry \\(\phi\\) of that game if \\( \phi(s) = s \\).

Then, respecting a set \\(\Phi\\) of symmetries simply refers to respecting each symmetry in \\(\Phi\\). We observe in the paper that any set \\(\Phi\\) of symmetries _partitions_ the set of all actions into the group-theoretic concepts of _orbits_, and that respecting \\(\Phi\\) reduces to assigning actions in the same orbit the same probability of play. Two actions are said to be in the same orbit if one can be mapped to the other by an arbitrary composition of symmetries in \\(\Phi\\). In Matching Pennies, the simple set {<span style="color: deepskyblue;">\\(\phi\\)</span>} already creates a single orbit \\(a_1 \rightarrow b_2 \rightarrow a_2 \rightarrow b_1 \rightarrow a_1\\); hence, there is only one strategy profile which assigns each of these actions the same probability: both players playing 50%-50%. In the color coordination game, the set of all symmetries in that game create two orbits: One that contains both player's red color, and the other that contains (Y,B,G) of both players.


## Nash Equilibria

The _Nash equilibrium_ is the central solution concept in game theory, and it requires that each player plays her best strategy given the strategy choice of the other player.

**Definition**: A strategy profile \\(s = (s_1,s_2)\\) is called a Nash equilibrium of a game \\((A,B)\\) if \\( s_1^TAs_2 = \\max_x x^T A s_2 \\) and \\( s_1^TBs_2 = \\max_y s_1 B y^T \\).

It is called a Nash equilibrium because John F. Nash Jr. proved via two different approaches that each game has a Nash equilibrium. In the simpler approach via the Brouwer fixed point theorem, Nash in fact proved more:

**Theorem** (Nash 1951): Each game has a Nash equilibrium that respects all symmetries of that game.

Our goal is to characterize how computationally hard it is to compute a Nash equilibrium that respects a given set \\(\Phi\\) of the game. In what comes, we are actually computing _\\(\epsilon\\)-approximate Nash equilibria_ to be precise, but for the sake of presentation, we will drop this detail, and refer to the full paper for a formal treatment.

# A Worst-Case Analysis

It has long been known (Gale, Kuhn, and Tucker 1952) that finding a symmetries-respecting Nash equilibrium cannot be of easier complexity in general than finding any Nash equilibrium, using the intuitive idea described in the introduction, in which we do not reveal to the participants of a game which player identity in it they might take on at the end (PL1 vs PL2). But we can give an even more striking example: Say we start with an \\(m \times m\\) utility matrix \\(A\\) with values in \\([0,1]\\). Append a column and row to it by defining
\\[ C = \begin{pmatrix} -10 & 2 & \dots & 2 \\\ 2 & & & \\\ \vdots & & A & \\\ 2 & & & \end{pmatrix}. \\] 
Then, the totally symmetric game \\((C,C^T)\\) is easy to solve for any Nash equilibrium: By looking through the utility matrices, it becomes clear (in linear time) that the best outcome for both players is for one to play her first strategy and the other to play a strategy that is not his first. If we were to restrict ourselves to equilibria that respect the total symmetry, however, then both players will have to play the same mixed strategy. In particular, we will first have to figure out the Nash equilibria of the totally symmetric "subgame" \\((A,A^T)\\); and this is---as we will discuss next---a computationally hard task (= not polynomial time, for all we know).

On the positive side, we can show that in general finding a Nash equilibrium that respects a set of symmetries _is not asymptotically harder_ than finding any Nash equilibrium of the game either! For context, this latter computational problem has been captured exactly by the complexity class PPAD.

**Theorem**: The problem of finding a Nash equilibrium that respects a set of symmetries is PPAD-complete. 

The complexity-theory community generally believes that PPAD-complete problems (1) cannot be solved in polynomial time, while still (2) being easier to solve than NP-complete problems (NP is this famous class containing all those problems for which we can verify in polynomial time whether a proposed point is indeed a solution to the problem). Our theorem implies that we can find symmetry-respecting Nash equilibria with fixed-point solvers and path-following methods, as these methods are well-suited to PPAD problems.

What can we say, on the other hand, about popular game subclasses, such as strictly collaborative and strictly competitive games? To start with the former, we consider _team games_ (also known as games with identical interst or common payoffs), in which all players always receive the same utilities, like in the color coordination game in the beginning. For this class, the phenomenon we described with the game \\((C,C^T)\\) becomes omnipresent: indeed, team games are generally guaranteed to have a _Pareto-optimal_ Nash equilibrium that doesn't randomize and is therefore computable in linear time. However, those strategy profiles might not respect most or any nontrivial symmetries present in the game (illustrated, again, by the coordination game). Instead, the constraint of respecting symmetries leaves us with the harder computational problem of non-linear continuous optimization. To illustrate, we have visualized below what the optimization problem looks like for a particular two-player player-symmetric game of three actions (__R__ ight, __L__ eft, __C__ enter).

<p align="center">
<img src="./kkt.png" alt="Gradient Descent in constrained settings finds a KKT point." width="300">
</p>

Instead of working in the strategy profile space---which is a product of two 3-simplices---, we are working in the _orbit profile space_---which is a single 3-simplex due to the total symmetry. The utility function that is a multilinear polynomial function over the strategy profile space now becomes an arbitrary polynomial function over the orbit profile space (_i.e._ it can contain variables with higher degree). The figure depicts the gradient field of that polynomial function. Projected gradient descent on this constrained optimization problem finds the strategy that plays \\( (60 \\% R, 40 \\% L, 0 \\% C)\\), and indeed, both players playing this strategy forms the only symmetry-respecting Nash equilibrium of the original game. We will leverage this connection to the orbit profile space more thoroughly later on. But for team games specifically, we are able to show that finding a symmetry-respecting Nash equilibrium is _exactly_ as hard as finding solution points to (projected) gradient descent on a convex polytope (also known as Karush-Kuhn-Tucker (KKT) points or first-order optimal points). That is, gradient descent (together with some appropriate preprocessing) forms a suitable method for this problem, and it is also the most efficient algorithm available for it---modulo polynomial time speedups and barring major complexity theory breakthroughs. Formally, this is captured by the complexity class CLS.

**Theorem**: In team games, the problem of finding a Nash equilibrium that respects a set of symmetries is CLS-complete. 


+++It has long been known (Gale, Kuhn, and Tucker 1952) that finding a symmetries-respecting Nash equilibrium cannot be of easier complexity in general than finding any Nash equilibrium: Say, we want to find any Nash equilibrium of a game \\(G = (A,B)\\), which we can assume to have strictly positive utilities without loss of generality. Then instead, we might consider the totally symmetric game \\( G' = (C,C^T)\\) defined as \\[ C = \begin{pmatrix} 0 & A \\\ B^T & 0 \end{pmatrix}. \\] This formalizes the intuitive idea described in the introduction, in which we may not want to reveal to the participants in \\(G\\) which player identity they might take on (PL1 vs PL2). In particular, in \\(G'\\) they have to specify a strategy \\(z = (x,y)\\) which represents what the participant would do in \\(G\\) if they take on the role of PL1 (play \\(x\\)) vs PL2 (play \\(y\\)). Then, Nash equilibria \\((z,z')\\) in \\(G'\\) that respect its total symmetry (that is, \\(z' = z = (x,y)\\)) correspond to Nash equilibria in \\(G\\). Hence, finding a symmetry-respecting Nash equilibrium cannot be easier in general than finding an (asymmetrical) Nash equilibrium.+++

# A positive story (change title)
In contrast to increased (yet managable) complexity in the case of strictly collaborative games, we are able to recover truly efficient algorithms for computing symmetry-respecting Nash equilibria in strictly competitive games. 

**Theorem**: In two-player zero-sum games (\\(A=-B\\)), we can find a Nash equilibrium that respects _all_ symmetries of the game in polynomial time. 

This result is stronger than all other results we discuss in this blog post because in its technical formulation, it does not require to know ahead of time which symmetries shall be respected. It finds a Nash equilibrium that respects all symmetries of the game via a clever convex programming approach, and without having to compute a single symmetry of the game. That we can do this task in polynomial time is surprising because we also showed in the paper that deciding whether a two-player zero-sum game even has a symmetry (aside from the identity function) is a computationally hard problem (graph automorphism hard to be precise, and therefore likely not doable in polynomial time).

Last but not least, we can show that if there is an abundance of symmetries in the game, then the number of orbits might be low enough for equilibrium computation to become easier. Consider, for example, the below 15-action variant of Rock Paper Scissors, taken from this [StackExchange](https://boardgames.stackexchange.com/questions/11280/rock-paper-scissors-with-more-weapons). An arrow \\(a \to b\\) indicates that \\(a\\) wins against \\(b\\).

<p align="center">
<img src="./rpsx.png" alt="A 15-action, highly symmetric variant of Rock Paper Scissors." width="300">
</p>

Then this game is highly symmetrical: it is player symmetric, and rotating the labels of the actions for both players simultaneously does not affect the winning relationships. Hence, all actions are in the same orbit. This renders the
task of finding a symmetry-respecting Nash equilibrium not only polytime but trivial, because there is only one strategy profile left that respects those symmetries: the one that plays all actions with the same probability, _i.e._, both players randomize uniformly. More generally, we can show:

**Theorem**: We provide an algorithm that whose sole exponential dependence is in the number of distinct orbits. Hence, if that is guaranteed to be bounded by a constant, the algorithm runs in polynomial time.

# Conclusion
The concept of symmetry is rich, with many applications across the sciences, and in AI in particular. For game theory, the situation is no different. Indeed, a typical course in game theory conveys the most basic concept of a symmetric (two-player) game; to check whether it applies, no more needs to be done than taking the transpose of a matrix. But there are other, significantly richer symmetry concepts as well, ones that require relabeling players’ actions or which do not allow arbitrary players to be swapped. We have studied the problem of computing solutions to games that respect these richer symmetry concepts. We have shown that requiring to respect them does not worsen the algorithmic complexity (significantly), and that it improves the complexity when the number of symmetries is vast. We also gave a strongly positive result for two-player zero-sum games.

# Footnotes
^1 For instance, randomize uniformly over (Y,B,G) in round 1. In rounds t ≥ 2, repeat last round’s action if both of you coordinated successfully last round; otherwise, repeat last round’s action only with 50% chance, and the other player’s action from last round with the other 50% chance.

# Bibliography
Brown, N.; and Sandholm, T. 2018. Superhuman AI for heads-up no-limit poker: Libratus beats top professionals. Science, 359(6374): 418–424.

Brown, N.; and Sandholm, T. 2019. Superhuman AI for multiplayer poker. Science, 365(6456): 885–890.

Gale, D.; Kuhn, H. W.; and Tucker, A. W. 1952. On Symmetric Games, 81–88. Princeton University Press. ISBN 9780691079349.

Liu, S.; Marris, L.; Piliouras, G.; Gemp, I.; and Heess, N. 2024. NfgTransformer: Equivariant Representation Learning for Normal-form Games. In The Twelfth International Conference on Learning Representations, ICLR 2024.

Marris, L.; Gemp, I.; Anthony, T.; Tacchetti, A.; Liu, S.; and Tuyls, K. 2022. Turbocharging Solution Concepts: Solving NEs, CEs and CCEs with Neural Equilibrium Solvers. In Advances in Neural Information Processing Systems 35, NeurIPS 2022.

Nash, J. 1951. Non-Cooperative Games. Annals of Mathematics, 54(2): 286–295.

Rawls, J. 1971. A Theory of Justice. The Belknap press of Harvard University Press.

Samuel, A. L. 1959. Some Studies in Machine Learning Using the Game of Checkers. IBM Journal of Research and Development, 3(3): 210–229.

Silver, D.; Huang, A.; Maddison, C. J.; Guez, A.; Sifre, L.; van den Driessche, G.; Schrittwieser, J.; Antonoglou, I.; Panneershelvam, V.; Lanctot, M.; Dieleman, S.; Grewe, D.; Nham, J.; Kalchbrenner, N.; Sutskever, I.; Lillicrap, T. P.; Leach, M.; Kavukcuoglu, K.; Graepel, T.; and Hassabis, D. 2016. Mastering the game of Go with deep neural networks and tree search. Nature, 529(7587): 484–489.

Silver, D.; Schrittwieser, J.; Simonyan, K.; Antonoglou, I.; Huang, A.; Guez, A.; Hubert, T.; Baker, L.; Lai, M.; Bolton, A.; Chen, Y.; Lillicrap, T. P.; Hui, F.; Sifre, L.; van den Driessche, G.; Graepel, T.; and Hassabis, D. 2017. Mastering the game of Go without human knowledge. Nature, 550(7676): 354–359.

von Neumann, J.; and Morgenstern, O. 1944. Theory of Games and Economic Behavior. Princeton University Press.


# Leftover

After filling in the above "top-matter", as per instructions provided
in the `.md` file, you can write the main body of the blogpost here
onwards. Commonly used examples of syntax are shown below.

You can run `./local_server.sh` at the root of the repository to see
how the final blogpost looks in action.

# Section Heading

## Subsection Heading

Some text.

## Another Subsection Heading

Some more text.
You can write lines
separately
and it'll still
be considered
a single paragraph. Paragraphs are separated by a
blank line.

# Another Section

You can **bold** things by wrapping them in two asterisks/stars. You
can _italicise_ things by wrapping them in underscores. You can also
include inline `code` which is done by wrapping with backticks (the
key likely to the left of the 1 on your keyboard).

If you want to add larger snippets of code, you can add triple
backticks around them, like so:

```
this_is_larger = true;
show_code(true);
```

However, the above doesn't add syntax highlighting. If you want to do
that, you need to specify the specific language on the first line, as
part of the backticks, like so:

```c
#include <stdio.h>

int main() {
   printf("Hello World!");
   return 0;
}
```

If you want to quote someone, simply prefix whatever they said with a
`>`. For example:

> If it is on the internet, it must be true.

-- Abraham Lincoln

You can also nest quotes:

> > You miss 100% of the shots you don't take
>
> -- Wayne Gretzky

-- Michael Scott

Every paragraph _immediately_ after a quote is automatically right
aligned and pressed up against the quote, since it is assumed to be
the author/speaker of the quote. You can suppress this by adding a
`<p></p>` right after a quote, like so:

> This is a quote, whose next para is a normal para, rather than an
> author/speaker

<p></p>

This paragraph is perfectly normal, rather than being forced
right. Additionally, you could also add a `<br />` right beside the
`<p></p>` to give some more breathing room between the quote and the
paragraph.

In the author notifications above, btw, note how the double-hyphen
`--` automatically becomes the en-dash (--) and the triple-hyphen
`---` automatically becomes the em-dash (---). Similarly, double- and
single-quotes are automagically made into "smart quotes", and the
ellipsis `...` is automatically cleaned up into an actual ellipsis...

---

You can add arbitrary horizontal rules by simply placing three hyphens
on a line by themselves.

---

Of course, you can write \\( \LaTeX \\) either inline by placing stuff
within `\\(` and `\\)` markers, or as a separate equation-style LaTeX
output by wrapping things in `\\[` and `\\]`:

\\[ \sum_{n_1 \in \N} \frac{n_1}{n_2} \\]

Alternatively, you can wrap it inside of a pair of double-dollar signs
`$$`:

$$ \frac{\Phi \in \psi}{\psi \rightarrow \xi} $$

Single dollar signs unfortunately do not work for inline LaTeX.

# More fun!

Of course, you can add links to things, by using the right syntax. For
example, [here is a link to NASA](https://www.nasa.gov/). Standard
HTML-like shenanigans, such as appending a `#anchor` to the end of the
link also work. Relative links within the website also work.

You can also use the links to link back to parts of the same
blogpost. For this, you need to find the "slug" of the section. For
this, you can force a slug at the section heading, and then simply
refer to it, like the [upcoming section](#finale), or alternatively,
you can take the lowercase version of all the parts of a section and
place hyphens between them, like [this](#more-fun) or
[this](#another-section).

Pictures, of course, can be added. The best way to do this is to
utilize relative links (just add images into the right directory, see
the main `README` file in this repository to learn where it should
go), but you can link to external images too in the same way. For
example,

![i are serious cat](https://upload.wikimedia.org/wikipedia/commons/4/44/CatLolCatExample.jpg)

Of course, it is good etiquette to add alt-text to your images, like
has been done in the previous image, with "i are serious cat". It
helps with accessibility.

Images are automatically shown at a reasonable size by limiting their
maximum width. If you have a particularly tall image, you might have
to do some manipulation yourself though. Images should also
automatically work properly in mobile phones :)

---

Do you want some tables? Here are some tables:


| Header 1   | Another header here   | This is a long header |
|:---------- | ---------------------:|:---------------------:|
| Some data  | Some more data        | data \\( \epsilon \\) |
| data       | Some _long_ data here | more data             |
| align left |   right               | center                |

You use the `:` specifier in the table header-body splitting line to
specify whether the particular column should be left, center, or right
aligned. All the standard markdown elements continue to work within
the table, so feel free to use them.

# Finale {#finale}

Finally, you're at the end of your blogpost! Your name will appear
again at the end automatically, as will the committee members who will
(hopefully) approve your blogpost with no changes! Good luck!
