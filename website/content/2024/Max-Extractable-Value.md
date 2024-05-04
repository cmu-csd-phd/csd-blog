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
   1. High gas fee for the network 
   2. Re-organization attack

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
1. For every 12 seconds, a validator (Frank) is selected randomly using RANDAO as proposer to build a block.
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
1. In a CPMM, the price of a token changes as users exchange in the liquidity pool
2. Each liquidity pool is independent from each other

Arbitrage is possible if a MEV searcher sees a user trying to exchange from ETH to USDC in DEX A, and this would result in the price change in DEX A. If DEX B offers the exchange between the same pair of token, searcher could immedietaly buy USDC in DEX B, sell it in DEX A and make profits described above. 

## Liquidation & Protocol Encouraged Tasks 
Lending Protocols, like aave, allows a user to collateral asset in one type to borrow in another. If one wants to exchange from one asset to another without suffering from the price change in DEX, they may choose lending protocols. For example, Alice may use 1500 USDC as collateral, put that in a lending protocol, and borrow 1 ETH 
