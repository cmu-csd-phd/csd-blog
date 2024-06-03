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

MEV, short for Maximal Extractable Value, represents the potential risk-free profit accessible to validators (or miners in Proof of Work) within blockchain network like Ethereum, stemming from their privileged access to unconfirmed transactions. In 2021, MEV generated an impressive $540M over 32 months (**cite**), and by 2024, this figure has surged to over $6 million per month(**cite**). In this blog, I'll discuss  
1. Common MEV Examples
2. Ehtereum Proof of Stake
3. Problems caused by MEV
4. Off-Chain Auctions between builders and searchers
5. Proposer Builder Seperation


# Common MEV Examples
Numerous MEV opportunities abound within decentralized finance protocols, particularly decentralized exchanges and lending platforms. In this section, I will elucidate several prominent MEV opportunities, beginning with an overview of the underlying mechanics of DeFi protocols.

We first use a simplified model to help understanding, where I assume that only two players exist in the MEV ecosystem: ordinary users and MEV searchers. MEV searchers could see ordinary users transactions before they are included into blocks.

## Arbitrage 
Decentralized exchanges (DEX) allow users to exchange from one token to another. However, if there're two exchanges supporting the same pair of tokens and offer different prices, there are risk-free profits. For example, the price for USDC/ETH is 1000 in DEX A, but 900 in DEX B.
1. A user could start with 900 USDC.
2. Get 1 ETH in DEX B
3. Use that 1 ETH to get 1000 USDC in DEX A
4. Result in a 100 USDC net income. 

A key question may raise at the points: how does a DEX decide its price?

### How does a DEX decide its price?
Various decentralized exchanges employ distinct formulas to determine the price of token pairs. For instance, let's delve into Unisapw V2, a renowned DEX. Uniswap deploys a program, commonly referred to as a smart contract, on the blockchain for each token pair, such as ETH and USDC. These smart contracts, akin to user addresses, can hold any quantity of tokens of any type. When a smart contract is engineered to accommodate various tokens, it's termed a liquidity pool. 

Initially the liquidity pool \\(A_C\\) will posses certain amount of ETH (reserve of ETH \\(r_E\\))  and certain amount of USDC (reserve of USDC \\(r_U\\)), and the amount is set by the deployer of the smart contract. Any time a user at address \\(A_U\\) could transfer \\(\Delta_E\\) of ETH to \\(A_C\\). This will trigger the exchange function in \\(A_C\\), resulting the DEX transfers \\(\Delta_U\\) USDC to the user where \\(r_E\times r_U = (r_E+\Delta_E)\times(r_U - \Delta_U)\\). This is called constant product market maker (CPMM) because at any time, the product of two tokens stays the same. 

There're also constant sum market maker, where \\(r_A+r_B = const\\), or generalized version of CPMM \\(\Pi {r_i}^{w_i} = const\\). As one can see, if there're only two kinds of tokens \\(i\in {1,2}\\) and \\(w_i = 1\\), it's the formula used by Uniswap V2. 

Two crucial points to note here are: 
1. In a Comstant Product Market Maker (CPMM) model, the price of a token fluctuates in response to users trading withint the liquidity pool.
2. Each liquidity operates independently of others.

Arbitrage opportunities arise when a MEV searcher observes a user attempting to swap from ETH to USDC in DEX A, causing a price shift in DEX A. If DEX B facilitates the same token pair exchange, the searcher can promptly purchase USDC in DEX B, sell it in DEX A, and capitalize on the price differential, thus yielding profits. 


## Liquidation & Protocol Encouraged Tasks 
Lending Protocols, like aave, allows a user to collateral asset in one type and borrow in another. If one wants to exchange from one asset to another without suffering from the price change in DEX, they may choose lending protocols. For example, Alice may use 1500 USDC as collateral, put that in a lending protocol, and borrow 1 ETH.

However, the prices of crypto currencies change all the time. When Alice stake their USDC initially, 1 ETH may only worth 1000 USDC. As the price of ETH increases, 1500 USDC may worth less than 1 ETH. In this case, to avoid bad debt, the protocol will sell Alice's collateral before the price of ETH reaches 1500 USDC. The exact selling point is called the liquidation threshold which is represented as the percentage of the total value of debt borrowed. Selling/buying someone's collateral to avoid bad debt is called liquidation. For aave specifically, the protocol will sell Alice's collateral when the price of ETH reaches 1237.5, corresponding to a liquidation threshold of 82.5%. 

In this case, any buyer buying 1500 USDC with 1 ETH when the market price of ETH is only 1237.5 USDC has a net profit of 262.5 USDC. This is a risk-free profit because the buyer could buy 1500 USDC with 1 ETH and sell that 1 ETH in the same transaction using smart contracts. Thus, the transaction will success only when both buying and selling success. 

Liquidation is a protocol encouraged tasks as lending protocols rely on searchers to ensure good financial health. There're other protocol encouraged MEV opportunities. One example could be fee distribution for Wild Credit. Wild Credit accumulate interests on their liquidity pools. The interests needs to be converted and distributed to liquidity providers by calling a function. Part of the interests is reserved for the function caller, and if the gas fee is less than the reserved interest, this is an MEV opportunity. 


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

Alice typically specify the minimum price she is willing to accept, such as "I want to receive at least 950 USDC for my 1 ETH!" She avoids setting a high minimum price like "I want to receive at least 1000 (or higher) USDC for my 1 ETH!" to prevent potential delays or transaction failures due to infeasible prices. The former ensures a smoother transaction process, while the latter could lead to frustration. 

If Alice sets her minimum acceptable price at 971 USDC for her 1 ETH, Bob could exploit this as an MEV searcher. By selling ETH before Alice, Bob could drive the price down to Alice's minimum, then but ETH after Alice's transaction. In the example below, we observe a net profit of 0.02 ETH from a 1 ETH transaction at a price of 1000 USDC/ETH. Once again, this is a risk-free profit, as all three transactions could occur in a single block, and if any one of them failes, all three transactios are reverted.  

| With Sandwich Trad  | ETH Reserve   | USDC Reserve | Product of Two Assets |
|:---------- :|: ---------------------:|:---------------------:|:----------:
| Before Alice  | 100      | 100,000 | 10,000,000|
| Tx 1: Bob      | 1 | -990             | / |
| After Bob |  101             | 99010             |10,000,000|
| Tx 2: Alice |  1           | -971             | / |
| After Alice |  102       |      98039       | 10,000,000 |
| Tx 3: Bob      | - 1.02          | 990             | / |
| After Bob |  100.98             | 99029             |10,000,000|

## Long-tail MEV opportunities
Arbitrage, sandwich trading, and liquidation are more common MEV opportunities. However, 80% of these three types of MEV have a profit between $0 - $10. Some MEV opportunities are much more rewarding but also much rarer. These opportunities often exploits loopholes in DeFi smart contracts, resulting a loss in liquidity pool instead of ordinary users. These attacks are fixed quickly though. 

For example, a well-known pump and dump attack happened to bZx protocol in ealry 2020 with a profit of $350,000, but after that, bZx quickly paused trading and borrowing on bZx and fixed the underlying bug. 

## Front Running
Finally, the last MEV opportunity we will discuss in this blog is the attack to attacks: For example, miners / validator could run all pending transactions locally, and if they see any one that's profitable, they will simply replace the receiving address of the profit to be the miner/validator's address. 

The native protection from front running would be hiding the receiving address from the transaction input, but instead stored the address in a smart contract. However, if the miner/validator is more sophisticated and goes into the logic of the smart contract this will not work. To protect searchers from being front-run, the current best solution to to seal the transactions until the validator has committed to include this transaction. And this will be explained in the next section when we go through proposer-builder seperation. 

# Ethereum Proof of Stake 
In the first section, we assumed a simple model with only two types of players: ordinary users and MEV searchers. Now, we will introduce another player: miners (in Proof of Works) or proposer (in Proof of Stake).

In the context of proof of stake, users stake 32ETH and become validators. Validators are responsible of collecting transactions from users, proposing new blocks, and voting blocks proposed by other validators. Validators need to run three pieces of software to finish tasks mentioned above: 
1. execution client
2. consensus client
3. validator client 

For a transaction to be confirmed in the blockchin, it needs a few steps. We use an example: Alice would like to confirm a transaction that says "Alice sends 3 eth to Bob" to explain the process.

Part A:
1. The transaction needs to be signed by Alice and Alice also needs to specify the amount of gas fee they're willing to pay for this transaction. The gas fee includes two parts: a base fee that is set by Ethereum netowrk depends on the current congestion level, and a tip (priority fee) for validators to encourage validators to include this transaction in the next block. The base fee will be burn and tip goes to validator. (Alice: 0.00002 eth in total with 0.00001 eth base fee)
2. Alice sends the signed transaction to an execution client (let's say Charle's execution client \\(C_e\\) .) \\(C_e\\) will check if Alice has signed this transaction, and if Alice has enough balance to pay for the gas fee. 
3. If \\(C_e\\) checks out on Alice's transaction, the transaction will be added to \\(C_e\\)'s mempool. In addition to that, \\(C_e\\) broadcasts the transaction to other execution clients (\\(D_e\\),\\(E_e\\),etc.) over the execution layer gossip network.

Part B:  
Once a transaction enters the mempool it will wait to be picked up. This happens in the following sequences:
1. For every slot (12 seconds), a validator (Frank) is selected randomly using RANDAO as proposer to build a block.
2. Frank's execution client \\(F_e\\) bundles the transactions from the local mempool into an “execution payload”. By default, \\(F_e\\) selects transactions with highest priority fee until the block is full. 
3. \\(F_e\\) passes the execution payload to its consensus client (\\(F_c\\))
4. \\(F_c\\) generate a “beacon block” with the “execution payload”, rewards, penalties, slashings, attestations etc and broadcast the “beacon block” to the consensus layer gossip network
5. Other consensus clients receiving the “beacon block” will pass it to their execution client to check the validity of the transactions 
6. The validator client attest the block by adding it to its local database and boardcast an attestation to the network.
7. It's worth noting that the transaction is not finalized yet. To fianlize blocks, validators need to vote for pairs of blocks at the beginning of each epoch (32 slots).

Before Ethereum switched to Proof of Stake, Proof of Work is used, and proposers were called miners in POW. 

## Priority Gas Auction
When MEV surged in 2019, Ethereum is still under POW. In many cases, more than one MEV searchers may find the same MEV opportunities, and competing for the block inclusion. 

As we mentioned above, in Part B Step 2, when \\(F_e\\) bundles the transaction from the local mempook into an “execution payload”. By default, \\(F_e\\) would pick the transactions with the highest priority fee to maximize their profit. 

MEV searchers, in this case, would run auctions publicly in the network for miners to include their transactions. For example, if searcher A and B found the same MEV opportunity that would result in a profit of 1 ETH. A and B would each braodcast a series of transactions with same content, but incremental gas fee. We call these transactions "bids" resembling bids in auctions. In theory, they're willing to pay for any amount of gas fee as long as it's less than 1 ETH.  This is termed priority gas auction (PGA).

In the graph below, we see two searchers: 0x6B...6542 and 0xb8...7a3f bidding for the arbitrage opportunity. We use triangles to represent a series of bids with different gas fee placed by 0x6B...6542, and circles for 0xb8...7a3f. The auction lasted 14 seconds, with both searchers gradually increase the gas bid from \\(25\\) gwei to roughly \\(8000\\) gwei. 

[Pic]

PGA resembles a first-price all pay auction since when two players are competing for the same MEV opporutnieis, and the second player's transactions will fail, nonetheless still need to pay for the gas fee for block inclusion. 

In our example, the auction winer and loser are the two transactions with \\(134\\)  and \\(133\\) gwei respectivly. Due to network delay, searchers were still updating gas fees after the transactions had been included.  


# Problems caused by MEV
Indeed, not all MEV transactions involve attackes; many of them are protocol encouraged tasks. Even for sandwith trading, where a 2% loss occurs in each transaction, it can still be advantageous compared to tranditional financial system where banks often charge between 0.5% to 5%. However, to extract past MEV, miners/proposers may re-org the chain history. This is an existential threat to Ethereum's consensus security. Less severly, with searchers competing for block space in the open network, Ethereum suffers network congestion and chain congestions. 

## Network Congestion
When two miners are competing for the MEV opportunities to be included in the block, each of them will reissue the transaction repeatedly with a higher gas fee. This could because of the bot's bidding strategy, or simply because the searcher noticed a higher bid in the peer to peer network. 

In our example above, 0x6B...6542 and 0xb8...7a3f issued 42 and 43 bids reslectivly. This significantly increased network congestion.


## Chain Congestion
As we explained in our example, the miner would include both searcher A's and B's transactions because even if the transaction failed, searcher still needs to pay for a percentage of the gas fee simply for block inclusion.

The block space is wasted by failed transactions, artifically increasing block scarcity, thus resulting a higher gas fee for ordinary users. 

## Time-bandit attack
A much more serious attack on Ethereum related to MEV is time-bandit attack. Proposers could re-propose a subchain to extract the MEV profits in it. For example, the current block height is 100. Instead of proposing block 101, proposers could propose block 51 to 100 again, so they could extract MEV profits in these 50 blocks.  

# Off-Chain Auctions between builders and searchers
To solve the network congestion and chain congestion brought by MEV, Flashbots built an off-chain, first price, sealed bid auction system between builders and searchers called MEV-geth. Instead of doing PGA in the open network, searchers would send bundles to miners/proposers. 

Bundles are one or more transactions that are grouped together and executed in a given sequences. It's encouraged for the searchers to set the gas price to be 0, and pay builders for the block inclusion fee by using a special transfer function in the bundle. Miners/proposers would select the bundles with the highest bid, and place this bundle at the top of the block -- winning bundle will be the first to be executed in a block -- thus guarenteeing the success of the execution.  

The atomic execution of the bundle could be guarenteed by using smart contracts, same as how searchers make profits risk-free, so searchers will only pay the miners/proposers if their bundles are executed succesfully.  

## What MEV-geth metigates
MEV-geth resolves the network congestion because all the communication between searchers and miners/proposers will not happen in the peer ot peer network. Meanwhile, MEV-geth also resolves the chain congestion because miners/proposers will not include failed transaction as searchers set the gas price to be 0. Inclusing a failed transaction will give no reward to miners/proposers. This is also preferred for searchers because they only pay miners/proposers if their MEV extraction is succesful. 

## What problems stay
First of all, MEV-geth didn't address time-bandit attack. Miners/Proposers are still incentived to re-org the subchain to extract MEV. Secondly, after Ethereum swiched to Proof of Stake in 2022, people started to notice that with searchers communicating to proposers off-chain, solo validators are making much less profits from MEV comparing with staking pool. 

In Ethereum Proof of Stake, validators could either be solo validators, or join a staking pool with other validators. Consider a solo validator with 32ETH staked, and a validity pool with 320ETH staked. While the pool has 10 times more opportunities to extract MEV profits because they're selected as proposers 10 more times than solo validators, the pool is much more sophisticated in exploiting MEV opportunities compared to solo validators because they could spend much more effort on optimizing profits for each time they're selected as proposer.

In order to help solo validators benifit from MEV, Vitalik proposed a system that outsources block building to a group of specialized player called builders. 



# Proposer Builder Seperation (PBS)
In our previous model, we have three players: searchers, ordinary users, and proposers. In this section, we will introduce builders, who is reponsible of preparing full blocks that will be proposed by proposers.

In the step 2 of Part B on how a transaction gets confirmed, the proposer's execution client \\(F_e\\) bundles the transactions from the local mempool into an “execution payload”. In PBS, \\(F_e\\) propose a full block built by builders instead of building the block themselves.

Anyone could be a builder. A builder is expected to build a block wigh highest profit, including MEV profit and priority gas fees. Builders would bid for block proposing by boardcasting a block header, which contains the commitment to a block body and specifying the amount of reward they are willing to pay the proposers. Proposer then commit on proposing a specific block by signing the block header. After seeing the signature from proposer, builders reveal the full block.  

To implement PBS on Ethereum, we need to update the fork choice rules. Currently, in a given slot, there are only two fork choices: either proposer boardcast a block, or not. However, with the aforementioned PBS proposal, Ethereum needs three fork choices:
1. Proposer didn't commit on any block header
2. Proposer commits on a block header, but builder didn't reveal the full block
3. Proposer commits on a block header, and the full block is revealed 

Therefore, a temporary solution is to implement an off-chain auction system between builders and proposers, where they could communicate off-chain on which block the proposer will propose. In this way, we keep the only two fork choices: either proposer boardcast a block, or not.



## MEV-boost: current off-chain implementation of PBS
Flashbot provided an OFF-CHAIN proposer builder seperation API called MEV-boost that outsources block building to builders. Since the auction system between builders and proposers happens off-chain, a doubly-trusted third party, relay, is needed here. 

MEV-boost works as below. In a given slot, 
1. Builders send the full block to relay. In the last transaction in the block, the builder transfers some amount of ETH to the proposer, this is the bid for block propose. 
2. Relay hides the details of the block, sends just block header and the amount of bid to proposer.
3. Pproposer commits to propose the block by signing the block header.
4. Upon seeing the signature from proposer, relay reveals the full block to proposer.
5. Proposer propose the block to other validator’s consensus client for voting.

[pic]  

In the current system, without a relay, builders cannot send the full block directly since proposers could propose the last transaction in the block only. If proposer still need to sign the header, there is no guarentee that the full block revealed by the builder includes the profit as promised. Relay here work as a middle man that checks on builders' block, and ensures the builders only pay when the block is proposed. It's similar to ebay as a doubly trusted party between buyers and sellers.


## More Problems 
A big problem with MEV-boost is the existence of doubly-trusted third party: relayers. Another problem that may exist in PBS (both with and without relays) is that proposers and/or builders may delay the block revealing time so they could have more time for MEV extraction. A known consequences to this behaviors is missed slot. 

In an honest case, a block should be proposed at the begining of the slot, and selected validators would vote on the block withint 4 seconds. However, a proposer could delay the release of the block such that just over 40% of selected validators voted on the block. With more time, they would be able to collect more transactions and also harvest the MEV profits on these additional transactions. This is called timing game. Timing game is possible, and profitable, but not exploited yet. (cite: https://arxiv.org/pdf/2305.09032) 



