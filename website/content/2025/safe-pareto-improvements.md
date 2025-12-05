+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "Safe Pareto improvements: Making everyone better off without taking chances"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2025-03-11

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Artificial Intelligence", "Theory"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
# Consider these similar to keywords specified for a research paper.
tags = ["game theory", "equilibrium selection problem", "computational complexity", "cooperative AI"]

[extra]
author = {name = "Caspar Oesterheld", url = "https://www.andrew.cmu.edu/user/coesterh/" }
# The committee specification is  a list of objects similar to the author.
committee = [
    {name = "Fei Fang", url = "https://feifang.info/"},
    {name = "Tuomas Sandholm", url = "https://www.cs.cmu.edu/~sandholm/"},
    {name = "Eric Sturzinger", url = "https://scholar.google.com/citations?user=3_-60QsAAAAJ&hl=en"}
]
+++

## Outline

 * I'll start by introducing the main idea behind safe Pareto improvements with an example (without game-theoretic terminology).
 * I then give some very basic background on game theory, both to motivate safe (Pareto) improvements and to describe safe Pareto improvements more precisely.
 * Using this language, I will then describe safe (Pareto) improvements more precisely, with further examples.
 * I'll overview some of the computational complexity results on safe (Pareto) improvements that I and others have proved.
 * Finally, I'll note some directions for future work.

> In some places, I provide supplementary material, which I format like the present sentence.


## Surrogate goals -- a motivating example for safe Pareto improvements
<a id="surrogate-goals"></a>

Let's say I bought an [NFT](https://en.wikipedia.org/wiki/Non-fungible_token), call it NFT1, off my friend Alice. Since then, the value of NFT1 has increased, so I don't want to reverse the trade. Alice now argues that I had some private information about how the price of NFT1 would develop and that it was unfair of me not to tell her that this private information is the reason I wanted to buy NFT1. Meanwhile, I argue that I did tell her and she just didn't pay attention. In any case, there's a dispute (and it's helpful to assume some ambiguity about who's in the right).

Additionally, let's imagine that -- despite still being interested in NFTs -- we live a few years in the future and so my assets are managed by some AI agent. (We could instead imagine that I hire a human to act in my interest in some sort of negotiation. But let's stick to AI in the following.)

Now I might worry that my AI agent will be subject to threats or attempts at bargaining over NFT1. For instance, I might currently be saving up for NFT2 that Alice has no interest in. Then Alice could threaten to buy and hold NFT2 unless my AI agent returns NFT1 to her (in exchange for the original payment); and my AI agent might give up NFT1 or, worse, Alice will buy NFT2. (If the threat of buying NFT2 is supposed to be effective, then Alice buying NFT2 must be worse for me than returning NFT1.)

Can I intervene somehow on the interaction between my AI agent and Alice to alleviate some of my worries? Specifically, let's imagine that in this situation my only possible method of intervention is to instruct my AI agent and that I can prove to Alice that I'm instructing my AI agent in a particular way.

>To give a concrete example of how this might work: Imagine that my AI agent is based on using some proprietary language model like GPT-4 or Claude that I query through an API. Then my instruction is simply a prompt. I might announce to Alice how I'm going to prompt the system. The prompt might include any email that Alice sends me with demands to reverse the trade of NFT1. I might also say that I'll add, say, the current values of various NFTs to the prompt, my current bank account balance, or a 500-word essay by me about why I am to be considered the rightful owner of NFT1. I might also specify on what date I will call the API. Such announcements are credible, because others can to some extent check later whether I indeed made my decision this way. If I deviate, people will be able to tell that I'm a liar and this would have negative consequences for me later.

![NFT blackmail without surrogate goals](./ByFN7b2oA.png)

One idea for a beneficial intervention is to commit my AI agent to never give in to Alice's threats. (So, if my agent is driven by a language model, I might simply include in its context an instruction that says: "never give in to Alice's threats".) However, in practice this often is not a satisfactory strategy. Purely intuitively, it seems implausible that Alice would just stand down and let me walk away with NFT1 if I commit first. Alice feels that I have treated her unfairly. By committing, I remove Alice's recourse. Surely, Alice will now feel even more wronged than before!

>Here's a more game-theoretic argument against committing not to give in. If Alice lets me get away with NFT1 too easily, then others might observe this, might conclude that Alice is a pushover, and might be more likely to treat her poorly in the future. More generally, I might worry that if I give my AI some instruction that makes it harder for Alice to get NFT1 from my AI, then Alice will want to retaliate in order to discourage others from similar moves in the future. (If you find the arguments in this paragraph unsatisfactory, you may still continue reading. This post does not hinge on any of this.)

A second idea is that Alice and I make a deal, bypassing the AI agent. For instance, Alice and I might just settle on some price in between the original sales price and the current value of NFT1 at which I then sell NFT1 back to Alice. But of course, to reach such a deal, I'd have to bargain directly with Alice and this negotiation might fail. But the whole point of offloading such a task to an AI system (or a human contractor for that matter) is to not have to think about the issue in question myself! If I want to negotiate with Alice, I have to directly think about the very tricky question of whether I owe Alice the item, whether I should be so afraid of Alice's revenge that I better give her the item back, and so on. I'd rather have my AI system sort this out. Also, if I believe that my AI system is very good at bargaining (e.g., because it knows all the best practices for bargaining), then I will worry that if I negotiate with Alice directly, I will achieve a worse outcome.

Enter surrogate goals, a special case of safe Pareto improvements. Let's say I select some other NFT on the market that is as expensive as NFT2 (the one I plan to buy), but that neither I nor Alice have any intention of buying. Call this NFT3. Then I give instructions along the following lines to the AI agent: "However much you want Alice not to buy NFT2, you should to an equal extent want Alice to not buy NFT3. Also, never give in to any threat by Alice to buy NFT2."

The idea behind this bizarre-seeming instruction is as follows. If my AI follows the above instruction, then in some sense, the interaction between my AI and Alice is entirely analogous to what it would have been under the default instruction. In particular, Alice can try to coerce my AI just as well as she could have under the default instructions. She just needs to make sure to threaten to buy NFT3 instead of NFT2. Thus, in contrast to the "never give in" instruction, Alice has no reason to retaliate against the use of this instruction. At the same time, I benefit from the use of the instruction, because now if Alice makes a threat and carries it out, no harm is done to me. Meanwhile, to my AI agent, the two possibilities are also the same.

![NFT blackmail with surrogate goals](./r1EtEbhi0.png)

Taking stock, we have found a way for me to intervene on the interaction between my AI agent and Alice that makes things better for me and doesn't make things worse for Alice. That is, we have found a [Pareto improvement](https://en.wikipedia.org/wiki/Pareto_efficiency) on the default interaction between my AI agent and Alice. A Pareto improvement is simply a way to make at least one player strictly better off, while making nobody else worse off. Importantly, we have found a Pareto improvement without making judgment calls about how the given games might be played (i.e., about whether I or my AI agent should give NFT1 back to Alice). For instance, we have avoided assigning a probability distribution over outcomes of the underlying game. We call this type of Pareto improvement a _safe_ Pareto improvement to signify that we can be quite sure that it is a Pareto improvement. It's not "just" at least as good for both players _in expectation_ with respect to some probabilistic beliefs about how the game will be played.

## Background: elementary game-theoretic ideas and notation

To present a more rigorous exposition to safe (Pareto) improvements, I will now introduce some elementary game-theoretic concepts.

### Normal-form games and how to play them

We're interested in interactions between strategic decision makers with conflicting preferences. The simplest such interaction is a so-called two-player _normal-form game_. A two-player normal-form game consists of a set of possible actions (\\(A_i\\)) for each of the players and utility functions \\(u_1,u_2\\) that map pairs of actions onto utilities (\\(A_1\times A_2\rightarrow \mathbb{R}\\)). Each player aims to maximize expected utility. In doing so, they have to guess how their opponent will choose, who in turn is of course guessing what they are doing.

Let's consider an example of such a game. If you've watched so much as a 5min YouTube video about game theory, you will have seen the [Prisoner's Dilemma](https://en.wikipedia.org/wiki/Prisoner%27s_dilemma). There's no point in producing yet another exposition of this decision problem. So, instead of the Prisoner's Dilemma, consider the below example of a game. Player 1 chooses between \\(a_1\\) and \\(b_1\\); Player 2 chooses between \\(a_2\\) and \\(b_2\\). The utilities are given in the _payoff table_ below. The first number in each cell represents Player 1's utility and the second number represents Player 2's utility. For instance, Player 1's utility if Player 1 plays \\(a_1\\) and Player 2 plays \\(b_2\\) is 0, as given by the top-right corner of the payoff table.

|             | \\(a_2\\)         | \\(b_2\\)         |
| ----------- | :-----------: | :-----------: |
| \\(a_1\\)       | \\(1,3\\)         | \\(0,1\\)         |
| \\(b_1\\)       | \\(0,5\\)         | \\(1,4\\)         |

Table 1. An example of a normal-form game.

What should Player 1 do? Looking at the payoff table, we can see Player 1's task is essentially to guess Player 2's action. If Player 2 is more likely to play \\(a_2\\), then Player 1 should play \\(a_1\\); if Player 2 is more likely to play \\(b_2\\), then Player 1 should play \\(b_1\\). So Player 1 should put herself in Player 2's shoes and ask what Player 2 would choose. In general, Player 2 would in turn have to form beliefs about Player 1. However, it turns out that in this game you can see that regardless of what Player 2 expects Player 1 to do, Player 2 prefers to play \\(a_2\\). If Player 1 plays \\(a_1\\), then it is better for Player 2 to play \\(a_2\\) than to play \\(b_2\\) (\\(3>1\\)); and if Player 1 plays \\(b_1\\), then it is also better for Player 2 to play \\(a_2\\) (\\(5>4\\)). (In game-theoretic terminology: \\(a_2\\) _strictly dominates_ \\(b_2\\) for Player 2.) Therefore, we would expect Player 2 to choose \\(a_2\\). In particular, Player 1 should expect Player 2 to play \\(a_2\\). Thus, Player 1 should play \\(a_1\\).

### The multiplicity of solutions

The above game has a unique _solution_, a single rational way to play the game. In more technical terms, which we won't need for most of this post, it has a single [_Nash equilibrium_](https://en.wikipedia.org/wiki/Nash_equilibrium). (Using more obscure technical terms, we can also say that each player only has a unique [_rationalizable_](https://en.wikipedia.org/wiki/Rationalizability) strategy.)

In general, one of the unique features of multiagent games relative to single-agent games is that they can have _multiple_ valid solutions and these different solutions can give the players different utilities. In game-theoretic terms, they may have many Nash equilibria.

I'll now introduce a simple example of the multiplicity of solutions. I will call it the _Demand Game_. (In game-theoretic terms, it is isomorphic to the [Game of Chicken](https://en.wikipedia.org/wiki/Chicken_(game)) and the Hawk-Dove game.) I will reuse this later to illustrate safe Pareto improvements.

Imagine that between two countries lies a desert. Both countries have laid claim to the desert, but since the desert is sparsely populated and economically insignificant, neither has paid much attention to these conflicting claims. Then one day, a mining company finds oil in the desert. Suddenly, the territorial status of the desert takes political center stage in both countries. Both countries now have to decide whether to demand the desert for themselves by militarily occupying it. (To keep it simple, let's ignore the possibility of splitting up the desert, although analogous questions arise w.r.t. the question of what fraction of the desert to demand.) Of course, both countries would like the desert. However, if both countries try to occupy a desert, they fight a costly war.

The normal-form game in Table 2 is a simplistic model of the interaction between the two countries.

|             | <span style="font-weight:normal">Demand</span> | <span style="font-weight:normal">Refrain</span> |
| ----------- | :-----------: | :-----------: |
| Demand      | \\(-8,-8\\)       | \\(2,0\\)         |
| Refrain     | \\(0,2\\)         | \\(0,0\\)         |

Table 2. The Demand Game.

Now let's try to perform some simple game-theoretic analysis. Should Player 1 (the "Row player") choose Demand or Refrain? Well, it depends on what Player 1 believes Player 2 to do. If Player 1 believes that Player 2 will likely play Demand, then Player 1's best response is to play Refrain. But if Player 1 believes that Player 2 will play Refrain, then Player 1 should better play Demand. (Specifically, let's say that Player 1 believes that Player 2 will play Demand with probability \\(p\in [0,1]\\). Then Player 1's expected utility for playing Demand is \\(-8p + 2(1-p) = 2 - 10p\\). Her expected utility for playing Refrain is \\(0\\). So Player 1 prefers playing Demand if she believes that \\(2-10p> 0\\), i.e., if \\(p< \frac{1}{5}\\). She's indifferent if \\(p=\frac{1}{5}\\) and that she prefers Refrain if \\(p > \frac{1}{5}\\).)

So Player 1 has to ask herself what Player 2 will do. But Player 2's situation is symmetric to Player 1's. That is, Player 2 prefers Demand if Player 1 is likely to Refrain; and Player 2 prefers Refrain if Player 1 is likely to Demand. So to decide what to play, Player 1 has to ask herself what Player 2 will play. But to figure out what Player 2 should play, one needs to figure out what Player 1 will play. And so on. So it seems that this line of reasoning doesn't solve this game for us.

Here's one way of thinking about what the players should play in the game. Each player should have (probabilistic) beliefs about what the opponent will play and should respond optimally to those beliefs. Furthermore, the beliefs should be accurate. A situation where this is the case is called a _Nash equilibrium_. It turns out that the Demand Game has multiple Nash equilibria, i.e., multiple ways for both players have accurate beliefs and respond optimally to these beliefs. Player 1 may play Demand under the belief that Player 2 will play Refrain, and Player 2 may indeed play Refrain under the (accurate) belief that Player 1 will play Demand. Conversely, Player 1 may play _Refrain_ under the accurate belief that Player 2 will play Demand, and Player 2 may play Demand under the (accurate) belief that Player 1 will play Refrain. In game-theoretic terms, (Demand, Refrain) and (Refrain, Demand) are both Nash equilibria of the game.

A third, stranger possibility is that both players randomize, playing Demand with probability \\(p=\frac{1}{5}\\) (and Refrain with probability \\(\frac{4}{5}\\)), and again accurately believing the other player to play Demand with probability \\(\frac{1}{5}\\). After all, if the opponent randomizes in this way, one is indifferent between Demand and Refrain, so that one might as well randomize between them.

Because the Demand Game has multiple solutions, two players could also fail to "coordinate" on one of these solutions. For instance, they might both play Demand, incorrectly expecting the opponent to play Refrain.

Strategic dynamics like those in the Demand Game (or the Game of Chicken) are extremely common in the real world. The above story (about the desert) illustrates territorial conflict. Many negotiations, like those in the [surrogate goals](#surrogate-goals) section, exhibit similar dynamics. (Committing to buying only at a low price is good unless the other side commits to only selling at a high price; and _vice versa_.) [Government shutdowns in the US](https://en.wikipedia.org/wiki/Government_shutdowns_in_the_United_States) show that players sometimes make conflicting demands at great costs. See also ["Schedule Chicken"](https://en.wikipedia.org/wiki/Schedule_chicken) for another, less dramatic real-world example.

## The problem of judging interventions on games
<a id="the-problem"></a>

Safe Pareto improvements address the following problem. Some group of agents (players) are going to strategically interact with each other, which for simplicity we will model as a normal-form game. By default they interact according to some normal-form game \\(G\\). Generally, we will imagine that \\(G\\) has a multiplicity of solutions. Before the agents interact, some third party (or perhaps some group of third parties) can intervene on \\(G\\), i.e., on how the players interact. For example, they could ban one of the agents from playing a specific action, or pay a player in case a particular outcome occurs (thus altering the payoff matrix), etc. The third party has an interest in the outcome of the game. For example, she could have her own utilities assigned to the outcomes or she might want to help the agents to achieve a good outcome. Call this third party the _principal_.

How should the third party intervene? That is, given some game \\(G\\) and some set of games \\(G_1',...,G_n'\\), is there some game \\(G_i'\\) that the principals should prefer to \\(G\\)? Relatedly, for any _given_ intervention, is the intervention good? That is, given two games \\(G\\) and \\(G'\\) should we prefer that the agents play \\(G'\\) rather than \\(G\\)?

This question is conceptually difficult because of the multiplicity of solutions introduced above. In general, it's hard to tell what will happen if the agents play any of these games. For example, imagine that by default the agents play the Demand Game above. Now imagine that a third party can intervene to make the players get constant utilities of \\(1.5\\) and \\(0.3\\) instead. Is this good for Player 1? Is it good for both players (i.e., is it a Pareto improvement)? Depending on which equilibria the agents play in the Demand Game, the interventions might be either good or bad. For example, if we expect that normally they'd play the randomized/mixed Nash equilibrium (in which both players receive a utility of \\(0\\)) then these constant utilities are an improvement for both agents, i.e., a Pareto improvement. If by default they'd play either (Demand, Refrain) or (Refrain, Demand) and are equally likely to play either of these, then the constant utilities \\(1.5\\) and \\(0.3\\) are an improvement for Player 1 (in expectation) but not for Player 2.

While the question is difficult, it is widely applicable. We intervene on strategic interactions all the time and these strategic interactions often have multiple solutions.

>**How do existing literatures judge interventions under the multiplicity of solutions?** Given how commonly the above problem arises, you might wonder how it is addressed in the literatures in which it arises. Here is a brief overview of existing approaches.
>
>Most straightforwardly, we can view the problem of choosing which game some other agents should play as just like any other strategic decision that we address with standard game-theoretic tools. This new game is now not a simultaneous game anymore -- first the principal chooses; then the agents observe the principal's choice (which determines which game they play) and respond. In game-theoretic terms, this is most naturally viewed as an [extensive-form game](https://en.wikipedia.org/wiki/Extensive-form_game) (rather than a normal-form game). From this perspective, the multiplicity of solutions would generally propagate to the principal's decision. That is, when deciding whether to let the representatives play \\(G\\) or \\(G'\\), the principal is permitted to choose either \\(G\\) or \\(G'\\), unless even the _best_ equilibrium of one game is worse than even the _worst_ equilibrium of the other game. So this perspective tends to not give us very definitive answers.
>
>In mechanism design, one usually makes assumptions about what equilibrium will be selected in any given game. For instance, one often assumes that the agents will play the best (for the principal) Nash equilibrium. (Compare the notion of the [_price of stability_](https://en.wikipedia.org/wiki/Price_of_stability) in this literature.) Often there is further justification for this assumption. For instance, in many mechanism design settings, the game consists in having players report information. Typically, mechanisms are set up so that the best-for-the-principal equilibrium consists in honest reporting. Arguably, honest reporting is an especially natural strategy (a [_Schelling point_](https://en.wikipedia.org/wiki/Focal_point_(game_theory))). Sometimes an analogous worst-case assumption is also made. (Compare the notion of [_price of anarchy_](https://en.wikipedia.org/wiki/Price_of_anarchy) in this literature.) But other assumptions have been used as well. For example, the literature on [K-implementation](https://arxiv.org/pdf/1107.0022.pdf) assumes that the agents play undominated strategies and that within these they play whatever strategies are worst for the principal.

## Safe (Pareto) improvements -- the general idea

Safe improvements are a new idea for deciding -- in some cases -- whether a given intervention is good. The central insight behind safe (Pareto) improvements is that in some cases that previously seemed intractable, we actually can intervene to improve the interaction between a set of agents in a way that doesn't hinge on assumptions about how the multiplicity of solutions is resolved by the agents in any individual game. Specifically, we use uncontroversial assumptions about how different games relate. We call these relations/assumptions _outcome correspondences_, because they are a list of implications of the form, “if playing this game results in outcome 1, then that game results in outcome 2”, etc. Here are two elementary examples of such assumptions:
 * Sometimes games contain actions that are clearly irrational. (For instance, in game-theoretic terminology, some pure strategies might be strictly dominated.) It seems reasonable to assume that such actions can be removed from the game without affecting how the game is played.

   In some sense, we have already applied an assumption of this sort when we analyzed the game in Table 1 above. We noted that Player 2 should never feel compelled to play \\(b_2\\). We then removed \\(b_2\\) from consideration and analyzed the new game _in lieu_ of the new original game. We found that in this new game Player 1 should play \\(a_1\\) and then took that conclusion to propagate back to the original game.
 * If two games are analogous/isomorphic, then we should expect them to be played analogously/isomorphically. For instance, consider the Demand Game (Table 2) and the game in Table 3. Upon careful examination, we can see that these games are _isomorphic_. That is, we can obtain the game in Table 3 from the game in Table 2 as follows: First, rename Player 1's actions Demand and Refrain to \\(b_1\\) and \\(a_1\\), respectively. Second, rename Player 2's Demand and Refrain to \\(a_2\\) and \\(b_2\\) respectively. Finally, increase each of Player 1's payoffs by \\(2\\). It seems intuitive that merely relabeling the actions shouldn't make a difference for how the game should be played. Also, since the players are expected utility maximizers, changing utilities by a constant shouldn't affect their behavior.

   It therefore seems plausible that the following outcome correspondence holds between the Demand Game and the game in Table 3:
   If (Demand, Demand) is played in the Demand Game, then (\\(b_1\\), \\(a_2\\)) is played in Table 3.
   If (Demand, Refrain) is played in the Demand Game, then (\\(b_1\\),\\(b_2\\)) is played in Table 3.
   If (Refrain, Demand) is played in the Demand Game, then (\\(a_1\\),\\(a_2\\)) is played in Table 3.
   If (Refrain, Refrain) is played in the Demand Game, then (\\(a_1\\),\\(b_2\\)) is played in Table 3.

|             | \\(a_2\\)       | \\(b_2\\)       |
| ----------- | :-----------: | :-----------: |
| \\(a_1\\)       | \\(\phantom{-}2,2\phantom{-}\\)       | \\(\phantom{-}2,0\phantom{-}\\)       |
| \\(b_1\\)       | \\(-6,-8\\)     | \\(\phantom{-}4,0\phantom{-}\\)       |

Table 3. A game that is isomorphic to the Demand Game (as given in Table 2).

>Bibliographic remarks: Neither of the above two assumptions are new to our work (although we use them differently from prior work). The idea that one can (repeatedly) remove strictly dominated actions to analyze a normal-form game is widely known to students of game theory. The idea is widely useful. For instance, actions that are removed by iterated elimination of dominated strategies cannot appear in any Nash equilibrium. To efficiently find the Nash equilibria of a game, it is therefore prudent to first eliminated dominated strategies.
>
>The idea that isomorphic games should be played isomorphically is less widely considered, in part because it is not immediately useful for solving a single given game. Nonetheless, it is discussed as a desideratum for equilibrium selection in Ch. 2.4 of Harsanyi and Selten's (1988) book "A General Theory of Equilibrium Selection in Games".

We can also combine outcome correspondence assumptions to infer new outcome correspondences. For example, if some game \\(G_1\\) is played in the same way as \\(G_2\\) (e.g., because \\(G_2\\) is obtained by eliminating a dominated action from \\(G_1\\)) and \\(G_2\\) is played in the same way as \\(G_3\\), then we can also infer that \\(G_1\\) is played in the same way as \\(G_3\\). If the original assumptions are uncontroversial, such inferred correspondences are also uncontroversial.

**Definition**: Given some outcome correspondence assumptions and some preferences (which may be a partial order) over outcomes of different games, we say that a game \\(G^s\\) is a _safe improvement_ on another game \\(G\\) if there is an outcome correspondence between \\(G\\) and \\(G^s\\) s.t. for each outcome \\(o\\) of \\(G\\), all outcomes of \\(G^s\\) associated with \\(o\\) are at least as good as \\(o\\) (as judged by the given preferences).

As a first example, the game of Table 3 is a safe improvement as judged by Player 1 on the Demand game.

A safe _Pareto_ improvement is simply a safe improvement where the "better than" relation is defined by the Pareto relation induced by the preferences of multiple players. That is, we prefer \\(a\\) over \\(b\\) if \\(a\\) is better than \\(b\\) for every player.

The game in Table 3 is a safe Pareto improvement on the Demand Game (Table 2), albeit one where only Player 1 strictly benefits. However, if we decreased Player 2's payoffs by, say, \\(1\\) in each outcome, then Table 3 would not be a safe Pareto improvement on Table 2 anymore. (It would remain a safe improvement for Player 1 on the Demand Game.)

The [surrogate goal intervention](#surrogate-goals) is another safe Pareto improvement. We have an outcome correspondence as follows: If in the default interaction between Alice and my AI agent, the outcome is that Alice gets my agent to return the item, then it seems that the outcome under the surrogate goal intervention will be the same. If in the default interaction, Alice buys NFT2, then under the intervention Alice would buy NFT3. And so on. Each outcome in the default game corresponds to an outcome of the new game, which is at least as good for both players. Under one of the outcomes, I'm better off in the new game.

## Example: A safe Pareto improvement in the Demand Game

We will here discuss an example of an SPI in the Demand Game (which we have introduced earlier). For a second example based on the Demand Game, which is also more similar to the initial surrogate goals example, refer to the SPI on the Demand Game in the introduction (and then in more detail throughout) the [SPI paper](https://www.andrew.cmu.edu/user/coesterh/SPI.pdf).

Consider the following variant of the Demand Game. Once more, two countries -- call them Aliceland and Bobbesia -- are contesting the desert between them. But in addition to deciding whether to insist on occupying the desert or not, they have to decide on whether their militaries are to keep prisoners of war until the end of the war or to let them go free more or less immediately. Each of the countries prefers to get their prisoners of war back immediately, but each country individually would slightly prefer to keep the other country's prisoners until the end of the war, because returned prisoners could contribute to the enemy's war efforts. This new game is represented in normal form in Table 4.

|                      | <span style="font-weight:normal">Demand, Free PoWs (DF)</span> | <span style="font-weight:normal">Demand, Keep PoWs (DK)</span> | <span style="font-weight:normal">Refrain \(R\)</span> |
|:-------------------------:|:--------------:|:-------------------:|:------------:|
| Demand, Free PoWs (DF)       |\\(-7,-7\\)           | \\(-9,-6\\)               | \\(2,0\\)          |
| Demand, Keep PoWs (DK)  | \\(-6,-9\\)          | \\(-8,-8\\)               | \\(2,0\\)          |
| Refrain \(R\)             | \\(0,2\\)            | \\(0,2\\)                | \\(0,0\\)          |

Table 4. Demand Game with Prisoners of War.

(The game-theoretically inclined reader may recognize that the return-or-not-return-prisoners part of the game is structurally a Prisoner's Dilemma.)

Let's say that all negotiations have ceased between Aliceland and Bobbesia. In particular, they can't by themselves reach any sort of prisoners' exchange deal. Given this, it seems that if the countries go to war, each of them would choose not to return prisoners. We might therefore expect that for the purpose of predicting what would happen absent outside intervention, we can consider the game in Table 5 instead of the game in Table 4. (The game in Table 5 is obtained from the game in Table 4, simply by removing the DF action.)

>For game-theoretic readers: Note that DK does not _strictly_ dominate DF. A rigorous, generalizable justification for removing DF therefore needs to be slightly more involved. For instance, we could imagine that the players first choose simultaneously whether to Demand or Refrain, and then in a second step choose whether to free prisoners or not only if both played Demand in the first round. Then we can remove DF by applying strict dominance to the subgame that arises when both players have chosen Demand.

|                     | <span style="font-weight:normal">Demand, Keep PoWs (DK)</span>  | <span style="font-weight:normal">Refrain \(R\)</span> |
| ------------------- | :-------------------: | :------------: |
| Demand, Keep PoWs (DK)  |  \\(-8,-8\\)              | \\(2,0\\)          |
| Refrain \(R\)             |  \\(0,2\\)                | \\(0,0\\)          |

Table 5. Demand Game with Prisoners of War, if we remove the action DF for both players.

Now take the perspective of the International Committee for Pareto Improvements (ICPI), an international organization made up of dozens of countries. The ICPI can tell countries to pursue or not pursue certain courses of action. For example, they could tell one of the countries not to occupy the desert. Additionally, the ICPI has a budget that they can commit to providing aid to Aliceland and/or Bobbesia. Alas, the ICPI can only act on universal agreement among its members, and while -- for the purpose of this conflict -- all members want only the best for Aliceland and Bobbesia, its members have widely diverging views on the conflict. Some members are much more closely allied with one country or the other. Additionally, the countries in the ICPI disagree about what will happen absent ICPI's intervention. Some believe that in the end Bobbesia will recognize Aliceland's historical ties to the desert and will therefore leave the desert to Aliceland. Others believe that Bobbesia's more aggressive culture will cause Aliceland to leave the territory to Bobbesia. Because of these divergent perspectives, straightforward proposals at the ICPI have failed. For example, one member proposed that a fair coin should be flipped and depending on the outcome, Aliceland or Bobbesia should get the desert. Needless to say, this proposal did not pass.

It seems that for a proposal to pass at the ICPI it has to be a safe Pareto improvement on the default game between Aliceland and Bobbesia. It has to be a _Pareto_ improvement over the default because it needs to be good for both Aliceland and Bobbesia (or else the champions of the disfavored country will veto). And it should be a _safe_ improvement, because otherwise there will likely be someone who disagrees that it is an improvement and who will therefore veto the proposal.

Here's a first idea for a proposal that we might hope will pass: The ICPI should tell both countries to return prisoners of war immediately in case there is a conflict. If adopted -- one might argue -- both countries would benefit: if it comes to a war, the war would be less terrible for both countries. If the countries don't go to war with each other, then the instruction makes no difference.

Perhaps this is "close enough". But arguably this proposed intervention isn't quite a safe Pareto improvement. The problem is that war is now slightly less of a risk to the two countries and so which of the outcomes obtain (war, Aliceland/Bobbesia gets the desert, nobody gets the desert) may change (or the probability distributions over outcomes might change).

Let's justify this a little more. By instructing Aliceland and Bobbesia to return prisoners, the ICPI essentially removes the DK strategy for both players so that the two countries effectively play the game in Table 6.

|                     | <span style="font-weight:normal">Demand, Free PoWs (DF)</span> | <span style="font-weight:normal">Refrain \(R\)</span>      |
| ------------------- | :--------------: | :------------: |
| Demand, Free PoWs (DF)      | \\(-7,-7\\)          | \\(2,0\\)          |
| Refrain \(R\)             | \\(0,2\\)            | \\(0,0\\)          |

Table 6. A variant of the Demand Game with Prisoners (Table 4) in which the players are barred from playing DK, i.e., from keeping prisoners.

In terms of the payoffs, this is almost the same as the game in Table 5. The only difference is that the respective (Demand, Demand) outcome is now less bad for both sides. Unfortunately, one might worry that the decreased risk will cause the two countries to compensate by accepting a higher probability of war. That is, if war isn't so bad, they might be more inclined to risk war. (In fact, the Nash equilibria of the two games are exactly equally good. Both games have pure Nash equilibria (Demand, Refrain) and (Refrain, Demand) with payoffs (0,2) and (2,0). Additionally, they both have a mixed equilibrium in which both players receive a utility of 0.)

> When an activity (such as going to war) becomes less risky, people tend to engage in the activity more, often in a way that eliminates the gains from decreasing the risk. For instance, some studies have found that promoting the use of bicycle helmets does not decrease head injuries because the helmeted bike less cautiously. In psychology, this phenomenon is known as [_risk compensation_](https://en.wikipedia.org/wiki/Risk_compensation), sometimes also called the Peltzman effect.

To make the new game an SPI, we have to make sure that the risk-benefit ratios between the two games are the same. For this, the ICPI needs to use payments. Intuitively, in the original, reduced game, the possible gain from demanding relative to refraining is 2 and the possible downside risk from demanding is a loss of 8. So the ratio between them is 4. If we decrease the risk of demanding relative to refraining, we must correspondingly decrease the gain of demanding relative to refraining. The ICPI can do this by paying countries for refraining. Specifically, let's say the ICPI pays each country 0.2 if they refrain. Then the possible gain from demanding is 1.8 and the possible downside risk from demanding is 7.2. The ratio between these is 4. Therefore, the strategic dynamics are again the same between the two strategic interactions.

|                     | <span style="font-weight:normal">Demand, Free (DF)</span> | <span style="font-weight:normal">Refrain \(R\)</span>       |
|:-------------------:|:--------------:|:------------:|
| Demand, Free (DF)      | \\(-7,-7\\)          | \\(\phantom{0.}2,0.2\\)        |
| Refrain \(R\)             | \\(0.2,2\phantom{0.}\\)          | \\(0.2,0.2\\)      |

Table 7. A variant of the Demand Game in which both players are barred from playing DK and any player who plays R receives a reward of 0.2.

A slightly more rigorous perspective is that this new game is isomorphic to the original game, with the action mapping DK \\(\mapsto\\) DF, R \\(\mapsto\\) R for both players; and utilities transformed by the affine function \\(x\mapsto \frac{9}{10} x + \frac{1}{5}\\) for both players.

Because the strategic dynamics are the same between the two games, it seems reasonable to expect them to be played analogously: If (DK, R) is played in the game in Table 5, then (DF, R) is played in the game in Table 7, and so on.

By inspecting each pair of corresponding outcomes, we can verify that each outcome in Table 7 is better than its corresponding outcome in Table 4/5. That is, (DF, DF) is Pareto better than (DK, DK), (R, DF) is Pareto better than (R, DK), and so on. Therefore, the game in Table 7 is a safe Pareto improvement on the game in Tables 4/5 and the ICPI can approve the respective intervention (i.e., instructing the countries to return prisoners if it comes to a war and paying the countries a small amount for refraining, as modeled by Table 7).

## Results on the complexity of identifying safe improvements

Besides getting a conceptual grasp on safe (Pareto) improvements, most of my work has focused on results on the computational complexity of finding safe (Pareto) improvements. I'll here sketch a small sample of these results.

In its most abstract, general form, the problem is defined as follows: Let's say we are given the following:
 * a default (normal-form) game \\(G_0\\) (that is played if we do not intervene);
 * a set of (normal-form) games \\(\mathcal{G}\\), representing the possible interventions;
 * a [partial order](https://en.wikipedia.org/wiki/Partially_ordered_set) over the outcomes of \\(G_0\\) and the outcomes of the games in \\(\mathcal{G}\\), representing the principals' preferences over outcomes;
 * some assumptions about outcome correspondences between pairs of games, i.e., assumptions of the following form: if playing \\(G_i\\) were to result in outcome \\(o_i\\), then playing \\(G_j\\) would result in one of the following outcomes: \\(o_j^1,...,o_j^k\\).

Then we are to decide whether some \\(G\in \mathcal G\\) is an SPI on \\(G_0\\). That is, do the given outcome correspondences imply that whatever outcome were to occur in \\(G_0\\), a better outcome (as judged by the given order) would occur in \\(G\\)?

All our results on the complexity of finding SPIs can be viewed as considering special cases of the above problem. The most straightforward is the unrestricted case with finite, explicitly represented inputs. It turns out that the problem of finding SPIs is [co-NP-complete](https://en.wikipedia.org/wiki/Co-NP-complete) in this case.

**Theorem 1** (informal, [Oesterheld and Conitzer, 2025](https://cgi.cse.unsw.edu.au/~eptcs/paper.cgi?TARK2025:36)): Consider the above problem with finite, explicitly represented set of games \\(\mathcal{G}\\), assumptions \\(\mathcal{A}\\) and preference ordering. This problem is co-NP-complete.

>Here's some very rough intuition for Theorem 1: Roughly, the games and outcome correspondences define a set of variables and binary constraints, i.e., constraints between pairs of variables. (The variables are the unknown outcomes of the games; the domains are the sets of possible outcomes of the games; the outcome correspondences are the binary constraints.) Finding a satisfying assignment for a such binary constraint satisfaction structure is well-known to be NP-complete. (It's the (binary) constraint satisfaction problem.) However, in the context of SPIs we are not interested in a single satisfying assignment, i.e., an assignment of games to outcomes that satisfies all the outcome correspondence assumptions. Rather, for any game \\(G\in\mathcal G\\), we are interested in whether all satisfying assignments have a particular property, namely, the property that the outcome assigned to \\(G\\) is better than the outcome assigned to \\(G_0\\). In other words, when evaluating whether a specific \\(G\\) is an SPI, the answer is "yes" if and only if there exists no assignment that satisfies the assumptions and additionally violates the SPI outcome correspondence between \\(G\\) and \\(G_0\\). This is, roughly, the complement of the binary constraint satisfaction problem. Therefore, the problem is co-NP-complete.

In other work, we have mainly considered more specific sets of assumptions, such as the isomorphism and dominance assumptions discussed above. Also, we have considered specific models of what kinds of interventions are allowed, such as banning specific actions from being taken (which was part of the Demand Game intervention above) or modifying the player's utility functions (as we have done in the case of the surrogate goals example in the introduction). In each of these cases, the set of games \\(\mathcal{G}\\) is not represented explicitly (as a list of normal-form games) but in some structured form, e.g., as: "all games that can be obtained from \\(G_0\\) by removing some actions". (Similarly, the partial order over outcomes and assumptions are specified concisely.) This changes the nature of the complexity-theoretic questions.

Generally, whenever we use the isomorphism assumption, we get some minimum hardness just from deciding whether two normal-form games are isomorphic: [Gabarro et al. (2011)](https://www.sciencedirect.com/science/article/pii/S0304397511006323) show that this problem is [graph-isomorphism complete](https://en.wikipedia.org/wiki/Graph_isomorphism_problem) (and thus perhaps [NP-intermediate](https://en.wikipedia.org/wiki/NP-intermediate), in between P and NP in terms of hardness). We thus get the following:

**Theorem 2** (informal, [Oesterheld and Sauerberg, 2025](https://arxiv.org/abs/2505.00783)): The following problem is graph-isomorphism-complete: Given two games \\(G\\) and \\(G'\\), decide whether we can infer from the isomorphism assumption that \\(G'\\) is an SPI on \\(G\\).

Finally, I'd like to give a result from the original SPI paper, which considers interventions on the agents' utility functions.

**Theorem 3** (informal, [Oesterheld and Conitzer, 2022](https://www.andrew.cmu.edu/user/coesterh/SPI.pdf)): The following problem is NP-complete: Given a normal-form game \\(G\\), decide whether there is a way to give the agents new utility functions that form a safe (Pareto) improvement on \\(G\\), as judged by the original utility functions in \\(G\\).

## Open questions and future work

Much of my work on SPIs analyzes the complexity of finding SPIs as illustrated in the previous section. This is a simple recipe for projects, especially if we vary the type of permissible intervention. That is, we might consider any type of intervention on a game (incl. settings already studied in other contexts). In the Demand Game, for instance, we considered budgeted outcome-conditional payments as a method of intervention. As far as I know, there are no results on computing SPIs in this setting. Another straightforward approach to extending the computational complexity work is to consider different models of games, e.g., concise games, extensive form games, partially-observable stochastic games. This will at least change the complexity of applying the isomorphism assumptions (see [Gabarro et al., 2011](https://www.sciencedirect.com/science/article/pii/S0304397511006323)). One may also vary the type of assumptions (as we have done in prior work), but this requires a little more creativity.

Both for varying the type of intervention and the type of assumptions, one important goal is to explore how broadly SPIs can be applied. In existing work, the applicability of SPIs hinges on opportunities for very powerful (and arguably rarely available) interventions (such as modifying the agents' preferences) or specific (arguably somewhat rare) structures in the underlying game (isomorphisms between different parts of the game). I hope that we can demonstrate the broader usefulness of the SPI concept by making further outcome correspondence assumptions (e.g., along the lines of [Oesterheld and Conitzer, 2025](https://cgi.cse.unsw.edu.au/~eptcs/paper.cgi?TARK2025:36.pdf), Assumption 4) and by exploring widely available but powerful-for-the-purpose-of-SPIs interventions (_à la_ [Oesterheld and Sauerberg, 2025](https://arxiv.org/abs/2505.00783), Section 4).

I'm also interested in more conceptual questions, including the following:
 * Relative to other attempts at improving the outcome of a game, _safe_ improvements stand out because they don't require probabilistic beliefs about how a game is played by default. To what extent are safe improvements compelling from a perspective of forming probabilistic beliefs about what outcomes will occur in different games and then maximizing expected utility relative to those beliefs? (I discuss this question in more detail [here](https://casparoesterheld.com/2024/07/28/a-gap-in-the-theoretical-justification-for-surrogate-goals-and-safe-pareto-improvements/). See [DiGiovanni and Clifton 2024](https://arxiv.org/abs/2403.05103) for some existing work on this question.)
 * In practice, finding _exact_ SPIs is often infeasible because of uncertainty about the agents' utility functions. For instance, consider the ICPI intervening on the Demand Game and in particular consider the ICPI's payments to whomever refrains. In practice, it seems difficult to determine the size of this payment exactly, because the ICPI might not know the exact utilities of any of the outcomes of the game. However, in practice it also seems fine for this payment to be slightly off. It seems useful to model this approximate nature of real-world SPIs. Is it more difficult to reason about approximate SPIs?

Finally, I'd be interested in work that connects SPIs more to the real world. Where in the world might we already see (approximate) SPIs? (For instance, when bodies like the UN set rules for countries to follow, do they typically institute rules that are SPIs?) What obstacles come up as we try to apply SPIs to real-world problems? For instance, how big of a problem is it that we can only achieve approximate SPIs in the real world?

## Acknowledgments

I thank Emery Cooper, Fei Fang, Jiayuan Liu, Vojta Kovarik, Tuomas Sandholm, Nathaniel Sauerberg, Johannes Treutlein and Eric Sturzinger for helpful comments on this post.
