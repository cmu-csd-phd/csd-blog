+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "Maximal Extractable Value in Ethereum"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2024-05-01

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Artificial Intelligence", "Graphics", "Programming Languages", "Security", "Systems", "Theory"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
# Consider these similar to keywords specified for a research paper.
tags = ["foobar", "cache-invalidation"]

[extra]
# For the author field, you can decide to not have a url.
# If so, simply replace the set of author fields with the name string.
# For example:
#   author = "Harry Bovik"
# However, adding a URL is strongly preferred
author = {name = "Your Name Here", url = "YOUR HOME PAGE URL HERE" }
# The committee specification is simply a list of strings.
# However, you can also make an object with fields like in the author.
committee = [
    "Committee Member 1's Full Name",
    "Committee Member 2's Full Name",
    {name = "Harry Q. Bovik", url = "http://www.cs.cmu.edu/~bovik/"},
]
+++

MEV (Maximal Extractable Value) refers to the amount of risk-free profit that a validator (miner in Proof of Work) could capture in the blockchain, like Ethereum, due to the early access of unconfirmed transactions in the network. Back in 2021, MEV yielded over 540M USD in 32 months (**cite**), and this number has increased to over 6M per month in 2024(**cite**). In this blog, I'll discuss 
1. How does a transaction get confirmed in the context of Ehtereum Proof of Stake  
2. Common MEV Examples
   1. Arbitrage
   2. Liquidation & Protocol Encouraged Tasks
   3. Sandwich Trading
   4. Front-Running 
3. Problems caused by MEV and its (possible) solutions
   1. High gas fee for normal users
   2. Proposer Builder Seperation

# Ethereum Proof of Stake 
In the context of proof of stake, users stake 32ETH and become validators. Validators are responsible of collecting transactions from users, proposing new blocks, and voting blocks proposed by other validators. Validators need to run three pieces of software to finish tasks mentioned above: 
1. execution client
2. consensus client
3. validator client 

For a transaction to be confirmed in the blockchin, it needs a few steps. We use an example: Alice would like to confirm a transaction that says "Alice sends 3 eth to Bob" to explain the process.
1. The transaction needs to be signed by Alice and Alice also needs to specify the amount of gas fee they're willing to pay for this transaction. The gas fee includes two parts: a base fee that is set by Ethereum netowrk depends on the current congestion level, and a tip for validators to encourage validators to include this transaction in the next block. The base fee will be burn and tip goes to validator. (Alice: 0.00002 eth in total with 0.00001 eth base fee)
2. Alice sends the signed transaction to an execution client (let's say Charle's execution client \\(C_e\\) .) \\(C_e\\) will check if Alice has signed this transaction, and if Alice has enough balance to pay for the gas fee. 
3. If \\(C_e\\) checks out on Alice's transaction, the transaction will be added to \\(C_e\\)'s mempool. In addition to that, \\(C_e\\) may broadcasting the transaction to other execution clients (\\(D_e\\),\\(E_e\\),etc.) over the execution layer gossip network; and may forward the transaction to specialized block builder for possible MEV profits. 
   
Once a transaction enters the mempool it will wait to be picked up. This happens in the following sequences:
1. For every slot (12 seconds), a validator (Frank) is selected randomly using RANDAO as proposer to build a block.
2. \\(F_e\\) bundle the transactions from the local mempool into an “execution payload” 
3. \\(F_e\\) passes the execution payload to its consensus client (\\(F_c\\))
4. \\(F_c\\) generate a “beacon block” with the “execution payload”, rewards, penalties, slashings, attestations etc and broadcast the “beacon block” to the consensus layer gossip network
5. Other consensus clients receiving the “beacon block” will pass it to their execution client to check the validity of the transactions 
6. The validator client attest the block by adding it to its local database.
    
This is the high-level overview on how a transaction gets included into a block. It's worth noting that the transaction is not finalized yet. To fianlize blocks, validators need to vote for pairs of blocks. 

# Common MEV Examples
Many MEV opportunities lie in decentralized finance protocols like decentralized exchange or lending protocols. Here I will explain a few well-known MEV opportunities, by first explaining how the underlying DeFi protocos work. 

## Arbitrage 
Decentralized exchanges (DEX) allow users to exchange from one token to another. However, if there're two exchanges supporting the same pair of tokens and offer different prices, there are risk-free profits. For example, the price for USDC/ETH is 1000 in DEX A, but 900 in DEX B.
1. A user could start with 900 USDC.
2. Get 1 ETH in DEX B
3. Use that 1 ETH to get 1000 USDC in DEX A
4. Result in a 100 USDC net income. 

A key question may raise at the points: how does a DEX decide its price?

### How does a DEX decide its price?
Different DEX uses different formulas to decide the price of a pair of token. Here, we will use a popular DEX - Uniswap V2 as an example. For every pair of token, for example ETH and USDC, Uniswap deploy a program (called smart contract) on the blockchain. The program has an address \\(A_C\\), just like users, and every address on the blockchain could possess any amount of tokens in any type. If a smart contract is designed to posess any amoun to toknes, we call it a liquidity pool. 

Initially \\(A_C\\) will posses certain amount of ETH (reserve of ETH \\(r_E\\))  and certain amount of USDC (reserve of USDC \\(r_U\\)), and the amount is set by the deployer of the smart contract. Any time a user at address \\(A_U\\) could transfer \\(\Delta_E\\) of ETH to \\(A_C\\). This will trigger the exchange function in \\(A_C\\), resulting the DEX transfers \\(\Delta_U\\) USDC to the user where \\(r_E\times r_U = (r_E+\Delta_E)\times(r_U - \Delta_U)\\). This is called constant product market maker (CPMM) because at any time, the product of two tokens stays the same. 

There're also constant sum market maker, where \\(r_A+r_B = const\\), or generalized version of CPMM \\(\Pi {r_i}^{w_i} = const\\). As one can see, if there're only two kinds of tokens \\(i\in {1,2}\\) and \\(w_i = 1\\), it's the formula used by Uniswap V2. 

Two key takeaways here are that 
1. In a CPMM, the price of a token changes as users trade in the liquidity pool
2. Each liquidity pool is independent from each other

Arbitrage is possible if a MEV searcher sees a user trying to exchange from ETH to USDC in DEX A, and this would result in the price change in DEX A. If DEX B offers the exchange between the same pair of token, searcher could immedietaly buy USDC in DEX B, sell it in DEX A and make profits as described above. 

## Liquidation & Protocol Encouraged Tasks 
Lending Protocols, like aave, allows a user to collateral asset in one type and borrow in another. If one wants to exchange from one asset to another without suffering from the price change in DEX, they may choose lending protocols. For example, Alice may use 1500 USDC as collateral, put that in a lending protocol, and borrow 1 ETH.

However, the prices of crypto currencies change all the time. When Alice stake their USDC initially, 1 ETH may only worth 1000 USDC. As the price of ETH increases, 1500 USDC may worth less than 1 ETH. In this case, to avoid bad debt, the protocol will sell Alice's collateral before the price of ETH reaches 1500 USDC. Selling/buying someone's collateral to avoid bad debt is called liquidation. For aave specifically, the protocol will sell Alice's collateral when the price of ETH reaches 1237.5, when Alice's debt worth more than 82.5% of their collateral. 

In this case, any buyer buying 1500 USDC with 1 ETH when the market price of ETH is only 1237.5 USDC has a net profit of 262.5 USDC. This is a risk-free profit because the buyer could buy 1500 USDC with 1 ETH and sell that 1 ETH in the same transaction, so the transaction will success only when both buying and selling success. 

Liquidation is a protocol encouraged tasks as lending protocols rely on searchers to ensure good financial health. There're other protocol encouraged MEV opportunities. One example could be fee distribution for Wild Credit. Wild Credit accumulate interests on their liquidity pools. The interests needs to be converted and distributed to liquidity providers by calling a function. Part of the interests is reserved for the function caller, and if the gas fee is less than the reserved interest, this is an MEV opportunity. 

Another question may rise here. What if two MEV searchers find the same opportunity? How do I make sure my transactions get selected by the miner/validator instead of someone else's?

### How to make sure the miner/validator includes your transactions? 
Initially, when MEV first appeared 2019, Ethereum was still using Proof of Work for consensus. MEV searchers would run auctions publicly in the network for miners to include their transaction. For example, if searcher A and B found an MEV opportunity that would result in a profit of 1 ETH. A and B would braodcast a series of transactions with incremental gas fee. This is a first-price all pay auction since when two players are competing for the same MEV opporutnieis, the second player's transactions will fail, but they still need to pay for the gas fee due to block inclusion. 

## Sandwich Trading
Another well-known MEV opportunit is sandwith traidng. As we mentioned above, when we exchange from one asset to another in DEX, the price of the assets depend on the amount of assets in the liquidity pool. For example, Alice would like to trade 1 ETH to USDC. When Alice sign the transaction, the DEX has 100 ETH and 100,000 USDC, she would expect 990 USDC if the DEX is a CPMM. 

| Ideal Case  | ETH Reserve   | USDC Reserve | Product of Two Assets |
|:---------- :|: ---------------------:|:---------------------:|:----------:
| Before Alice  | 100      | 100,000 | 10,000,000|
| Tx 1: Alice      | 1 | -990             | / |
| After Alice |  101             | 99010             |10,000,000|

However, if Bob sells 1 ETH before Alice, this would result the liquidity pool has 99,010 USDC and 101 ETH, and by the time Alice sells her 1 ETH, she could only receive 971 USDC. Alice cannot be sure when will her transaction being included in a block -- there might be pending transactions in the mempools, or simply Bob pays higher priority fee.

| Actual Case  | ETH Reserve   | USDC Reserve | Product of Two Assets |
|:---------- :|: ---------------------:|:---------------------:|:----------:
| Before Alice  | 100      | 100,000 | 10,000,000|
| Tx 1: Bob      | 1 | -990             | / |
| After Bob |  101             | 99010             |10,000,000|
| Tx 2: Alice |  1           | -971             | / |
| After Alice |  102       |      98039       | 10,000,000 |

Alice normally would specify the worst price she could accept, for example "I want to receive at least 950 USDC for my 1 ETH!" Also, Alice doesn't want to say "I want to receive at least 1000 (or higher) USDC for my 1 ETH!" because this may results in longer waiting time for her transaction to be included into a block, or even transaction failure if this price is infeasable. The former is unplease while the latter is very frustrating. 

If Alice indeed specifies that the worst price she could accpet is 971 USDC for her 1 ETH, Bob could be an MEV searcher, by selling ETH before Alice, pushing the price to Alice's worst price, and buying ETH after Alice. In the example below, we see a net profit of 0.02 ETH with 1 ETH transaction in the price of 1000 USDC/ETH. Again this is a risk-free profit as all three transactions could be done in one block and any one of them failes, the whole block failes. 

| With Sandwich Trad  | ETH Reserve   | USDC Reserve | Product of Two Assets |
|:---------- :|: ---------------------:|:---------------------:|:----------:
| Before Alice  | 100      | 100,000 | 10,000,000|
| Tx 1: Bob      | 1 | -990             | / |
| After Bob |  101             | 99010             |10,000,000|
| Tx 2: Alice |  1           | -971             | / |
| After Alice |  102       |      98039       | 10,000,000 |
| Tx 3: Bob      | - 1.02          | 990             | / |
| After Bob |  100.98             | 99029             |10,000,000|

## Front Running
Finally, the last MEV opportunity we will discuss in this block if the attack to attacks: miners / validator could run all pending transactions locally, and if they see any one that's profitable, simply replace the receiving address of the profit to be the miner/validator's address. 

The native protection from front running would be hiding the receiving address from the transaction input, but instead stored the address in a smart contract. However, if the miner/validator is more sophisticated and goes into the logic of the smart contract this will not work. To protect searchers from being front-run, the current best solution to to seal the transactions until the validator has committed to include this transaction. And this will be explained in the next section when we go through proposer-builder seperation. 

# Problems caused by MEV and possible solutions
Not all MEV transactions are attackes. Many of them are protocol encouraged tasks. Even for sandwith trading, 2% loss for each transaction is still better in tranditional financial system where banks charge between 0.5% to 5%. However, with searchers competing for spots in a block on opne network, normal users will be seriously affected due to high gas fee. 

## High Gas Fee Due to MEV
Back to 2020, all MEV transactions need to be communicate publicly on the open network with other transactions from normal users. As we described in "How to make sure the miner/validator includes your transactions," searchers would start with small gas fee, and gradually increase it when they see someone else's transaction also competing for this MEV opportunity. 

The miner would include both transactions because even if the transaction failed, searcher still needs to pay for a percentage of the gas fee simply because her transaction is included in the block. 

This would result in miners selecting MEV transactions and their competitors due to the high gas fee they offer while leaving few space for normal users. This is an existential crisis for Ethereum. 

## Proposer Builder Seperation (PBS)
In PoW, Flashbot provided an off-chain communication channel between miners and searchers that moved the gas auction away from the open network. In PoS, Flashbor upgraded to an OFF-CHAIN proposer builder seperation API called MEV-boost that outsources block building to builders, and allows builders to reveal the block only after validators has commited on which block they will propose. 

In MEV-boost, there are three players:
1. proposer(the selected validator's consensus client): users who have staked 32 ETH and get selected to propose the next block. Proposers are randomly selected and they're responsible for proposing a block to be voted by other validators.
2. builder: block builders preparing a full block, including MEV transactions and/or transactions from normal users. Builders could be searchers, or they could connect to some searchers and prepare a full block with the highest profit. 
3. relay: relay functions as a trusted third party between builders and proposers. 
   1. Builders send the full block to relay
   2. Relay hides the details of the block, sends just the amount of profit and block hash to proposers. 
   3. The proposer commits to propose the block by signing the block. 
   4. Upon seeing the signature from proposer, relay reveals the full block to proposer. 
   5. Proposer broadcast the block to other validator's consensus client for voting. 

[Pic]  

### What MEV-boost mitigate
MEV-boost mitigate a few problems caused by MEV.
1. Searchers no longer pay for the failed execution. Since searchers and builders are colluded and the auction process happens off-chain, searchers and builders would coordinate to make sure block space optimizes the net profit. 
2. Normal users are not competing with MEV searchers on gas price. Again, since the auction process happens off-chain, normal users are only competing with other normal users in terms of gas price. 
3. Solo validators could also benifit from MEV. Solo validators may not be able to develop sophisticated techniques in finding MEV opportunities. By connecting to a relay and simply finds the block with highest profit, solo validators could also benifit from MEV.
4. Builders are protected from being fron-run by validators. Trusted relays work as a middle man that on the one side protects the builders from being fron-tun, and on the other side protects the validators from being scamed by builders and not sharing the promised revenue. 

### What problems stay 
A big problem with MEV-boost is the existence of doubly-trusted third party: relayers. To get rid of relays, one solution would be updating the Ethereum's fork choice rules. Currently, because the communication between proposers and builders happened off-chain, there're only two forck choices: either proposer boardcast a block in time, or not. By implementing PBS direcly on Ethereum without a third party relay, there will be three fork choices:
1. Proposer didn't commit on any block header
2. Proposer commits on a block header, but builder didn't reveal the full block
3. Proposer commits on a block header, and the full block is revealed 


Another problem that may exist in PBS (both with and without relays) is that proposers and/or builders may delay the block revealing time so they could have more time for MEV extraction. A known consequences to this behaviors is missed slot. In an honest case, a block should be released at the begining of the slot, and selected validators would vote on the block withint 4 seconds. However, a proposer could delay the release of the block such that just over 40% of selected validators voted on the block. With more time, they would be able to collect more transactions and also harvest the MEV profits on these additional transactions. This is called timing game. Timing game is possible, and profitable, but not exploited yet. (cite: https://arxiv.org/pdf/2305.09032) 



