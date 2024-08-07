+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "Efficient Anonymous Blocklisting"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2024-07-31

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Security", "Systems", "Theory"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
# Consider these similar to keywords specified for a research paper.
tags = ["cryptography", "zero-knowledge", "snark", "anonymity"]

[extra]
# For the author field, you can decide to not have a url.
# If so, simply replace the set of author fields with the name string.
# For example:
#   author = "Harry Bovik"
# However, adding a URL is strongly preferred
author = {name = "Orestis Chardouvelis", url = "https://orestischar.com/" }
# The committee specification is simply a list of strings.
# However, you can also make an object with fields like in the author.
committee = [
    {name = "Bryan Parno", url = "https://www.andrew.cmu.edu/user/bparno/"},
    {name = "Justine Sherry", url = "https://justinesherry.com/"},
    {name = "Noah G. Singer", url = "https://noahsinger.org/"},
]
+++

## TL;DR: 
* Truly Anonymous Service Providers can offer users confirmed privacy, but also allow inappropriate behavior 😳
* Anonymous Blocklisting permits blocking ill-behaved users without denanonymizing them. Specifically, the service provider blocks individual posts, and the benign users use zero-knowledge arguments (zk-SNARKs) to prove that they didn't make said posts, without revealing any information about them 😮
* The more blocked posts you have the less efficient the blocklist is, making it practically infeasible 😞
* SNARKBlock reduces the cost to logarithmic with respect to the size of the blocklist by introducing HICIAP, aggregating all the individual proofs into one efficient proof 🙌
* You can now live out your anonymous double life 😎

# Introduction  

The goal of this blog post is to teach the reader the fundamentals behind anonymous blocklisting, as well as to introduce a state-of-the-art blocklisting algorithm called SNARKBlock. In the conclusion, I will reflect on open problems for future anonymous blocklisting algorithms.

## Anonymous Communications Systems

Anonymous communications systems bring benefits but also harms. Computing users' private information has always been vulnerable to irresponsible corporations and identity theft. On top of that, oppressed citizens living under authoritarian governments struggle to maintain their privacy and risk facing prosecution for speaking out, while political journalists have to fight to keep their sources hidden. Anonymous communications systems aim to help these users by keeping their identities private from other observers.
The largest network that allows anonymous communication to date is [Tor](https://svn-archive.torproject.org/svn/projects/design-paper/tor-design.pdf), which utilizes "onion routing", encrypting the data multiple times and passing it through a network of different nodes, making it difficult to trace back to the source. Unfortunately, malicious users can take advantage of the gift of anonymity resulting in online bullying and harassment, trolling, and the spread of harmful or illegal content without consequences. The problem is the following:

*If no one knows who you are, no one can stop you.* 
<!-- <p></p> -->

How can internet services provide anonymity to users without allowing inappropriate behavior?
Many service providers claim to be anonymous but have often been criticized for storing the user's information, or metadata that can help identify them.<!--, like [Whisper](https://whisper.sh/) and [Blind](https://www.teamblind.com/). Another example is--> For instance, [Wikipedia](https://www.wikipedia.org/) provides weak anonymity by connecting a user's personal information to a pseudonym instead of directly storing it. Thus, all of their actions (e.g., page edits) are publicly linked to their profile, and analyzing patterns in editing behavior or content preferences could lead to inferences about their identity. 
One existing solution to linked metadata is using "revocable anonymity systems", which allow for a user to be deanonymized or pseudoanonymized (having their actions linked) when necessary. For example, imagine if Wikipedia users were completely anonymous (i.e., without a public pseudonym), but if one of your edits is deemed “inappropriate”, your anonymity is stripped and your identity is revealed. This type of system typically relies on a Trusted Third Party aware of the identity of the user and capable of revoking a user's privacy at their discretion.

## Anonymous Blocklisting 
Anonymous blocklisting systems come to the rescue to enforce policies on users without deanonymizing them. These systems allow users to authenticate anonymously with a service provider, while service providers can revoke a user's access without learning any information about their identity or involving a Trusted Third Party. Anonymous blocklisting systems can achieve blocking users from posting again by flagging individual posts instead of their accounts.

A way to realize this is to provide each user with a secret identity, and every one of their posts is secretly linked to that identity. Unlike the example with the Wikipedia users, there is not a public pseudonym connected to them, and their identity remains hidden even from the service provider. Whenever a user wants to post they have to prove that none of the flagged posts are linked to their identity, without leaking any information about it.

A savvy reader (you) can spot an immediate problem; how can we prevent users from making many different accounts? This is a common network service attack called the [Sybil Attack](https://www.freehaven.net/anonbib/cache/sybil.pdf).  In a "normal" system, users have to register through an identity provider (e.g., Google) using some identifier (e.g., their Gmail account). To solve this problem, blocklisting schemes can also utilize identity providers who would maintain a log of "registered users". Hence, when a user posts, they have to also prove they are registered without revealing it's them posting, using ~~magic~~ cryptography.

To summarize, anonymous blocklisting systems achieve blocking anonymous users without the need to deanonymize them. They allow users to post anonymously (even to the service provider), while service providers can block individual posts without any of the user's information getting leaked.

# Cryptographic Protocols

To delve deeper into the mechanics of anonymous blocklisting schemes, we'll go over some cryptographic protocols that help ensure the users' privacy.

## ZK-SNARKs
The main building block needed to build an anonymous blocklisting scheme is called a [zk-SNARK](https://www.di.ens.fr/~nitulesc/files/Survey-SNARKs.pdf); Zero-Knowledge Succinct Non-Interactive Argument of Knowledge. Even if it is a mouthful, every single property is necessary. Let's break them down together below. Assume we have two parties denoted as the Prover and the Verifier.
* Argument of Knowledge: A SNARK is a proof[^1] where the Prover can prove their possession of some information to the Verifier. Typically, the "information" is the solution ("witness") to a computational problem that the Verifier could not solve by themselves.<!-- without knowledge of the information they are proving possession of.-->
* Non-Interactive: The communication between the two parties solely consists of a single proof message sent from the Prover to the Verifier (in more general models, the Verifier and Prover could engage in multiple rounds of interactive communication).
* Succinct: The Prover’s message should be small compared to their witness.
* [Zero-Knowledge](https://people.csail.mit.edu/silvio/Selected%20Scientific%20Papers/Proof%20Systems/The_Knowledge_Complexity_Of_Interactive_Proof_Systems.pdf): The Prover manages to prove possession of their witness without revealing any information about the witness itself.

The crux of the whole protocol is the zero-knowledge property which can accompany a SNARK. To make Zero - Knowledge more tangible we can revisit one of the most overdone examples in the history of ZK, drawing from the world of [Avatar: The Last Airbender](https://www.imdb.com/title/tt0417299/)[^2]. Imagine our Prover is Aang, and our Verifier is Toph. Aang has two different colored boomerangs (one red and one green) and wants to prove to Toph who is (color)blind that they are indeed different colors. However, Aang doesn't want to let Toph know which boomerang is which color! Thankfully, they came up with the following Zero-Knowledge Protocol: Toph holds the boomerangs behind her back. She briefly displays one of the two boomerangs before hiding it again. She then again chooses one of the two at random, brings it out, and asks "Did I switch the boomerangs?". Of course, Toph knows if she displayed the same or a different boomerang, and Aang can easily differentiate given their different colors. If Aang lies, he will only succeed 50% of the time. By repeating the protocol multiple times, Toph can be convinced, without actually learning any information about the individual boomerang's colors!

<!--<img src="https://media.giphy.com/media/v1.Y2lkPTc5MGI3NjExdW4wYmRsaDZkcnkzbHNpbzc1OW40djVmbDkxN3B5d2t0azd5cXllciZlcD12MV9naWZzX3NlYXJjaCZjdD1n/4IzOgM1bfOe6k/giphy.gif" width="45%"/>-->
<img src="toph.gif" width="40%"/>

Of course in this example, even though we demonstrate the ZK property, this is not a SNARK since it is interactive. With a ZK-SNARK, Toph and Aang would not need multiple rounds of communication.

## Signature Schemes

Another cryptographic protocol required to understand anonymous blocklisting is a [signature scheme](https://people.csail.mit.edu/rivest/pubs/GMR88.pdf). A digital signature, just like a real-life signature, gives a Prover the ability to sign a message before sending it. Then a Verifier, using some public information, can verify that the Prover was the one who sent that message. Signature Schemes consist of 3 algorithms:
* Generation Algorithm<!-- \\( Gen(\lambda) \leftarrow (sk,vk) \\)-->: It produces a signature (secret) key *sk* only known by the signer and a verification key *vk* public to everyone.
* Signing Algorithm<!-- \\(Sig(sk, m) \leftarrow \sigma\\)-->: Given a message *m* and the secret key *sk*, it produces the digital signature σ.
* Verification Algorithm<!-- \\(Ver(vk, m, \sigma) \leftarrow \{0,1\}\\)-->: Given the public verification key *vk*, the original message *m* and the signature σ, it produces 1 if the signature is valid and 0 if it's not.

Signature schemes allow users to authenticate the origin and integrity of a message. Let's understand their importance through another Avatar example, where Zuko is trying to capture the Avatar[^2]. Imagine Zuko wants to announce to the world online, and as an extension his dad -the Firelord-, that he caught the Avatar. However, anyone can try and give false information, impersonating Zuko, and claim the Avatar has been caught. To avoid this scenario, Zuko sets up a digital signature scheme; he runs the Generation algorithm and shares the (public) verification key with his dad before his trip. Now, if he catches the Avatar, he can publish his message "I caught the Avatar, and with him, my honor", along with a signature σ. As a result, the Firelord can run the (public) verification algorithm, which would return true if this message is truly from Zuko, or false, indicating it did not, in fact, come from Zuko.

<img src="https://media.giphy.com/media/v1.Y2lkPTc5MGI3NjExb28zZW5yaHozNjd0NmM5MGdudnZ6dWMwYmxuYjQxamVwdjZhMWlrZyZlcD12MV9naWZzX3NlYXJjaCZjdD1n/kN2THUm8712diLwn0F/giphy.gif" width="50%"/>


## Commitment Schemes

We will also encounter a [commitment scheme](https://www.cs.cmu.edu/~mblum/research/pdf/coin/), which allows one to commit to a specific value while keeping it hidden from everyone else. In addition, the committed value can be revealed later without any possibility of alteration. This ensures both confidentiality and integrity, ensuring that the committed value is securely locked and that after revealing it, the original commitment and the revealed value match perfectly. Commitment schemes consist of the following two phases, which take place between a committer and a receiver:
* The commit phase, during which the committer chooses and commits to a value by producing a "commitment" message.
* The reveal phase, during which the committer sends the value to the receiver along with a "decommitment" message (e.g. the randomness used in the commit phase), and the receiver can verify its authenticity.

Commitment schemes have to satisfy two properties:
* Hiding property: Given a commitment, no information about the committed value can be extracted.
* Binding Property: The value chosen in the commit phase is the only one that the commitment can decommit to.

Assume that Aang and Toph are playing a game where Toph thinks of a number between 1 and 10, and Aang tries to guess it. They want to ensure that Toph cannot change her pick after Aang makes his guess, so they use a commitment scheme. Toph thinks of the number 7 and sends a commitment to Aang. Then Aang makes his guess and says: "I think the number is 5". Finally, Toph reveals her pick by sending a decommitment message. Due to the properties of the commitment scheme, Aang cannot cheat and get any information about Toph's number before the reveal phase. At the same time, if Aang guessed 7 correctly, Toph cannot lie about her initial pick claiming it was a different number.

<!--Assume that Aang wants to correctly guess how many guards Suki can take down, without letting her know beforehand. However, Suki doesn't trust him, so they use a commitment scheme. Soka guesses 42 and produces and sends a commitment message to Suki. After the fight, Aang reveals his answer, while also sending a decommitment message. Now, if the real number of guards was 43, Soka could not change his answer and still convince Suki he was right. At the same time, Suki cannot get any information about Aang's answer before the reveal phase and change her actions during the fight.

![suki](https://64.media.tumblr.com/5fe3d1ed55146768d4aabbb7a419f132/9b647a9d5c31eada-f0/s250x400/4814c265ff350458f9beb79eb4b7fe62509590ef.gifv)-->

## Pseudorandom Functions (PRFs)

The last protocol we will refer to is a [pseudorandom function](https://www.wisdom.weizmann.ac.il/~oded/X/ggm.pdf), or PRF. A PRF is a function that takes as input a key and a message, and returns a random-looking string: _PRK(key, message) = pseudorandom string_. A PRF must have the following two properties:
* It is easy to compute (i.e., in polynomial time).
* One cannot distinguish between random strings and the results of a PRF without access to the key.

In other words, randomness is expensive; PRFs are cryptography's efficient way of faking randomness.

# Anonymous Blocklisting

We will now focus on anonymous blocklisting schemes, starting with their necessary properties and continue by doing a survey of state-of-the-art systems [SNARKBlock](https://eprint.iacr.org/2021/1577.pdf) and its predecessor [BLAC](https://dl.acm.org/doi/pdf/10.1145/1880022.1880033).

Overall, in an Anonymous Blocklisting Scheme, there is a blocklist filled with flagged posts. Every user gets a "secret identity" when they register for the service. Every time they want to post, they have to produce a token that is linked to their identity, and then prove both that they are registered and that none of the flagged posts were made by them. To do that, as we will see later, they can use zero-knowledge proofs, attesting to the fact that their identity is valid (produced during the registration) and that it is not connected to any of the posts in the blocklist, without revealing any actual information about their identity. 

## Definition
We will begin with a simplified definition of anonymous blocklisting schemes due to [Henry and Goldberg](https://cacr.uwaterloo.ca/techreports/2010/cacr2010-24.pdf) that can be generalized to most existing blocklisting schemes.
<!--Time to get a bit more technical and see what the requirements and properties of an anonymous blocklisting scheme are. In the literature, there exist numerous definitions that are often too specific to the scheme in question, or too informal. For the purposes of this blog, we are going to draw from [Henry and Goldberg](https://cacr.uwaterloo.ca/techreports/2010/cacr2010-24.pdf) and present a simplified version that can be generalized to most existing blocklisting schemes. Let's start with the parties involved:-->
The parties involved are the following:
* Users: The set of individuals using the service are called users. All users are assigned to a random unique identifier _k_, which constitutes their identity and remains secret.
* Identity Providers: Every user has to connect to an identity provider (e.g., Google) to register for the service and acquire a new and valid identity.
* Service Providers: The entity (or entities) providing the service (e.g., Wikipedia).
* Revocation Authorities: The authority responsible for flagging content and blocking users. For the context of this blog, we assume the service providers also play the role of the revocation authorities, which is the case for most blocklisting schemes. 

The protocols that can take place in an anonymous blocklisting scheme are:
* Registration Protocol: This protocol takes place between a user and an identity provider and happens once so that the user registers for the service. By running this algorithm, the user receives a valid unique identifier. 
* <!--* Token Extraction Protocol: To anonymously connect a user every time they use a specific service use (e.g. post), the user has to run this protocol with their unique identifier to get an authentication token. As a result, every token is connected to their identity-->Token Extraction Protocol: For a user to take action on the service (e.g., post), they need an authentication token. By running this protocol with their unique identifier, they can obtain a token secretly linked to their identity. This process ensures that the token can be used for authentication while preventing anyone from gaining information about the user's identity by merely observing the token.
* Authorization Protocol: In this protocol, the service provider takes as input an authentication token and verifies that the user is eligible to use the service (i.e., not blocked).
* Revocation Protocol: This protocol is run by the service provider, taking as input an authorization token and blocking the user by adding the token to the blocklist.
* Reinstatement Protocol: Similarly to the revocation protocol, the service provider can also unban a user by removing their token from the blocklist. 

The crux of the anonymous blocklisting scheme is ensuring the following three security requirements:

* Blocklistability: Users can successfully authenticate to an honest service provider only if that user holds a valid identity not in the blocklist issued by an identity provider: Specifically, it encompasses the following two notions:
    1. Verification should succeed only on authentication tokens that are the result of a user correctly executing the established protocols.
    2. Given an authentication token issued to some anonymous user, a service provider can have the user’s access revoked, such that they cannot post again until all his banned tokens are removed. 

* Anonymity: No information about the user can be linked to an authentication token, which encompasses the following two notions:
    1. Given an authentication token from one of two users, it should be infeasible for an attacker to determine which user that authentication token was issued to.
    2. Given two or more authentication tokens, it should be infeasible for an attacker to distinguish if they came from the same user or two different ones.

* Non-frameability: An honest user cannot be prevented from being authenticated by an honest service provider.

Let's go back to our example setting[^2] to better better the mechanics of such a scheme. Imagine that the officials of the city of Ba Sing Se have set up an anonymous forum of people sharing secrets from their everyday lives, like the app Whisper, and Joo Dee is an identity provider. Assume that Aang wants to subscribe to the forum and make posts. He first has to get in contact with Joo Dee to register. As an outcome, he gains a unique identifier _k_, secret even to Joo Dee. Then, assume he wants to post the message "There is war in Ba Sing Se". He runs the token extraction protocol using his identifier to get a token α and anonymously sends the message along with the token to the city officials. Now they run the Authentication Protocol, verify that the message is not coming from a banned user, and publish it.
Of course, it's not long before the message gets flagged for harmful content. So the authorities run the revocation algorithm using that token. Now, if Aang tries to post again with a new token, it won't be authorized. However, no one can link his message to him or any of his futile attempts to post again.  

<img src="https://media.tenor.com/SOnmo9jnfQsAAAAM/avatar-the-last-airbender.gif" width="45%"/>


## Inefficient Constructions
As usual in cryptography, things in practice are a little different, and by different, I mean worse. The security requirements explained above are necessary but not sufficient for a useful in-practice anonymous blocklisting scheme. The size of the blocklist can grow extremely fast depending on the use case. 
For example, Wikipedia has approximately [2 edits per second](https://stats.wikimedia.org/#/en.wikipedia.org/contributing/edits/normal|bar|2020-11-04~2021-11-24|~total|monthly) and Reddit around [64 comments per second](https://old.reddit.com/r/blog/comments/k967mm/reddit_in_2020/). Estimating from event logs from 2020, the ban rate for Wikipedia is around 1%, which would result in approximately 2 thousand bans in Wikipedia and 40 thousand bans for Reddit.

We thus need schemes that are efficient, both for the users and the service provider. 

On the user's side, to be efficient means that authenticating a token and using the service has a predictable runtime and bandwidth so as not to add too much latency to their requests. On the service provider's side, we need both the authentication and revocation processes to have predictable running times and bandwidth, so that the cost of servicing a user is not too high and the system can keep up with the expected rate of revocations.

Let's start with a construction inspired by the first anonymous blocklisting scheme with a Trusted Third Party, [BLAC](https://dl.acm.org/doi/pdf/10.1145/1880022.1880033) by Tsang et al., to delve deeper into the mechanics[^3].
Consider the blocklist as a set of tokens, where every token is of the form _(nonce, PRF(k, nonce))_ for some random number _nonce_ and someone's unique identifier _k_.

The **registration protocol** has to take place once, before the user can access the service. The user randomly chooses his credential _k_, then computes and sends a commitment _com(k)_ to the identity provider. The identity provider answers with a signature _σ_ on that commitment. 

During the **token extraction protocol**, the user randomly chooses a value _nonce_ and computes a token _α = (nonce, PRF(k, nonce))_, tying the token with their identity.

The **authorization protocol** works as follows: the user sends to the service a token _α_, along with a zk-SNARK that: (i) the token is computed correctly and is equal to _PRF(k, nonce)_, (ii) they have a well-formed commitment _com(k)_ such that it is signed from an identity provider and (iii) none of the tokens in the blocklist are related to the user's identifier, i.e. <!--\\( \forall \alpha=(nonce^\prime, h) \in blocklist,  PRF(k, nonce^\prime) \ne h \\)--> _for all α=(nonce′, h) in the blocklist,  PRF(k, nonce′) ≠ h_. 

Then, in the **verification protocol** the service provider checks that the proofs are valid (i.e., the user is not blocked), and only then offers their service.

Finally, for the **revocation protocol**, if the service provider notices harmful content, they add the token accompanying it in the blocklist. Respectively, they can remove it if they decide to unban them by running the **reinstatement protocol**.

It is clear to see the security of this protocol:

* The scheme satisfies **blocklistablity** since, if a user is blocked or tries to use fake credentials, their zk-SNARK wouldn't verify. That is, there would either be a token in the blocklist connected to their unique identifier _k_, or they wouldn't have a valid signature on the commitment of their identifier. Also, because of the binding property of the commitment scheme, they cannot connect a different value to the signed commitment σ from the identity provider. At the same time, the service provider can block any user by adding their corresponding token to the blocklist.

* The scheme is also **anonymous**, since all the information sent to the service provider is through a zk-SNARK, revealing no information about the user. In addition, due to the hiding property of the commitment scheme, the identity provider also never learns anything about the user's identity.

* As far as **non-frameability** goes, for an honest user to be prevented from using the service, one would have to produce a token that would tie to the user's unique identifier, impossible given the pseudorandomness of the PRF.

However, there is an immediate efficiency flaw in the above construction; the server has to do linear work in the size of the blocklist to verify a user since the proof goes over the whole blocklist every time. At the same time, the proof sizes are also linear in the size of the blocklist. In BLAC, a single proof for a blocklist with 4 million blocks (a size that according to our previous estimations, Reddit would reach in approximately 100 days) would require a client to upload 549MiB of data. Overall, existing zk-SNARK implementations are fit to only handle pieces of the blocklist efficiently. 

# SNARKBlock

Enters [SNARKBlock](https://eprint.iacr.org/2021/1577.pdf), a new anonymous blocklisting scheme from Rosenberg et al. The authors build upon the aforementioned construction and can offer proofs that are only logarithmic in the size of the blocklist, while also requiring logarithmic verification time. 

Blocklists mostly stay immutable and the service provider adds to them. As a result, both the service provider and the users end up recomputing a lot of the information. More specifically, if a user has calculated a proof for a blocklist with 99 blocked posts, after a new post gets added they have to calculate a new proof for all 100 posts. 
The authors break up the blocklist into non-overlapping chunks so that users can reuse their proof computation over the unchanged chunks. Then they can combine all the distinct proofs into one logarithmic-sized proof (in relation to the blocklist size). 
So for our example, we could separate the blocklist into 10 chunks and only have to recompute the proof for the last 10 blocked posts.

There are two immediate problems with the above technique. To begin with, in the original protocol, the proof that was attesting to the validity of the user posting was taking as input the user's unique identifier as a witness, making sure that they have not posted any of the blocked posts. What happens though with proofs for different chunks? Each proof would have to take as input the witnesses anew, and a malicious user could potentially have a different identity for a specific chunk, bypassing the block. 

Another less obvious problem is the need for rerandomization over the proofs. Reusing a proof for a specific chunk can reveal information that connects the user with previous posts. There are indeed SNARK proofs that allow rerandomization, like the [Groth16](https://eprint.iacr.org/2016/260.pdf) scheme used in SNARKBlock. Nevertheless, the same cannot be said when presenting multiple proofs with a common hidden input.

Both of these problems are solved with the introduction of HICIAP.

## HICIAP
The main contribution of SNARKBlock is a new type of zero-knowledge proof, called HIdden Common Input Aggregate Proofs, or HICIAP (pronounced “high-chop”). With HICIAP, one can aggregate many zk-SNARKs (specifically Groth16 proofs) of the same relation into a single logarithmic-sized proof and show that they all share a common hidden input. At the same time, it is possible to link multiple HICIAP proofs of different relations, showing in a zero-knowledge proof that those inputs are equal. For our setting, this means that we can (i) have different proofs for each chunk of the blocklist that we aggregate to a single proof and (ii) link that proof with the other distinct proofs to make sure the same secret identity was used for all of them.

Let's see now how SNARKBlock's protocol differs from the BLAC-inspired inefficient construction. The authors separate the Authentication protocol into **Sync**, which is run by the user offline (i.e., before the authentication has to go through) performing necessary pre-computation, **Attest**, where the user produces and sends the token along with a zk-SNARK to prove eligibility, and **Verify**, where the service provider finally authenticates the user if the SNARK verifies correctly. Overall, the user can gather all the different proofs for each chunk and wrap them in a HICIAP proof, proving they share a common input. Later they can link this HICIAP proof with the rest of the proofs related to honest token extraction and registration.

More specifically, in **Sync**, the user starts by fetching the most recent version of the blocklist and its division into chunks. Then they compute:
* a proof \\( \pi_{chunk_i} \\) for each chunk of the blocklist that was altered or updated, proving that the user's unique identifier is not correlated with any of the blocks in that chunk; i.e., if the user's identifier is _k_, for all blocks _α = (nonce′, h)_<!--\\( \alpha=(nonce^\prime, h) \\)--> in the chunk, _PRF(k, nonce′) ≠ h_<!--\\( PRF(k, nonce^\prime) \ne h \\)-->
* a proof \\( \pi_{isu} \\) attesting to having registered, i.e. having a witness for a commitment signed by the identity provider

When it's time to use the service, the **Attest** protocol takes place. The user does the following:
* computes a proof \\(\pi_{token}\\) after they have extracted a token α, to prove that the token was computed honestly using their unique identifier _k_, _α = (nonce, PRF(k, nonce))_
* wraps the \\( {\pi_{chunk_i}} \\) proofs for all chunks, \\( \pi_{isu} \\) and \\(\pi_{token}\\) proofs into HICIAP proofs \\( \hat{\pi_{chunk}} \\), \\( \hat{\pi_{isu}} \\) and \\(\hat{\pi_{token}}\\) respectively
* produces a proof \\( {\pi_{link}} \\) that all of the aforementioned HICIAP proofs share the same witness, their unique identifier _k_
* sends \\( \hat{\pi_{chunk}} \\), \\( \hat{\pi_{isu}} \\), \\(\hat{\pi_{token}}\\) and \\( {\pi_{link}} \\) to the service provider.

Finally, the service provider checks the validity of the proofs during the **Verification** part.

## Efficiency
As noted before, SNARKBlock is much faster than BLAC, since both the verification time and proof size become logarithmic instead of linear in the size of the blocklist. In BLAC, a blocklist with 4 million bans would require a proof of 549MiB, whereas a SNARKBlock attestation for the same size blocklist is only 130KiB, making it feasible for use without elaborate hardware! But does this automatically make SNARKBlock efficient enough to be used in practice? We also cannot forget the extra cost SNARKBlock introduces: offline synchronization.

Here we can see the authors' evaluation of different-sized blocklists. These include the synchronization time depending on how much the blocklist was altered, the attestation time (which translates to how much time the user takes to produce a proof), the verification time on the service provider's side, and the size of the proof, with or without the use of different sized buffers[^4].

<!-- add pictures -->
<figure>
 <img src="sync.png" alt="Image 1" style="display: inline-block; width: 45%; margin-right: 1%;">
 <img src="attestation.png" alt="Image 2" style="display: inline-block; width: 45%; margin-right: 1%;">
 <img src="verification.png" alt="Image 3" style="display: inline-block; width: 45%;">
 <img src="proof_size.png" alt="Image 3" style="display: inline-block; width: 45%;">
 <figcaption style="text-align: center;"><a href="https://eprint.iacr.org/2021/1577.pdf">SNARKBlock's evaluation</a> from the paper: (top left) synchronization time depending on blocklist alterations, (top right) attestation time, (bottom left) verification time, and (bottom right) proof size depending on the blocklist size.</figcaption>
</figure>

More specifically, the top left figure shows the offline computation a client must do as a function of the number of changes to the blocklist. This includes syncing chunks and precomputing a proof that they are registered through an identity provider. We can see that the offline precomputation can take up to a couple of minutes for a large number of additions. Since the user can perform it asynchronously and periodically, it doesn't introduce any significant overhead.

The top right figure shows the time clients take to attest to non-membership on a blocklist that has recently changed. This is the time it takes for a user to recompute the last chunk proof and link them all together. These results can be interpreted differently considering the different services that SNARKBlock can be used for; if the time to write a message and send it to get posted is smaller than the authentication time (a few seconds here) then the message would get queued. These times seem to be acceptable for forums primarily focused on posting and commenting anonymously. However, the results are impractical for implementations like real-time chat forums, where speed is of the essence and attestation needs to be on the order of milliseconds. 

The two bottom graphs show the throughput and proof sizes for server verification. These graphs are in a semi-log scale and do in fact show that SNARKBlock proofs scale logarithmically with the number of elements in the blocklist, both in terms of size and time efficiency on the server's side.

<!--The only way to judge the scheme's usability is to consider what service it is being used for. If the time to write a message and send it to get posted is smaller than the authentication time, then the message would have to get queued. From the authors' evaluation, the times could be acceptable for forums primarily focused on posting and commenting anonymously. However, the results are impractical for implementations where speed is of the essence, like real-time chat forums. -->

# Conclusion
Anonymous communication systems protect user privacy but face challenges in managing inappropriate behavior. Anonymous blocklisting schemes, powered by advanced cryptographic protocols like zk-SNARKs, enable blocking individual posts without revealing user identities. These schemes use signature and commitment schemes, along with pseudorandom functions, to maintain privacy while ensuring message authenticity. 

SNARKBlock addresses inefficiencies in traditional systems by introducing HIdden Common Input Aggregate Proofs (HICIAP), which aggregate multiple proofs into a single efficient proof. This innovation achieves logarithmic proof sizes and verification times in relation to the size of the blocklist, making anonymous blocklisting practical for some large-scale applications, such as social media platforms. 

However, further advancements are needed to fully realize a world where anonymous blocklisting schemes are seamlessly deployed and used in everyday applications. Future steps include examining the use of [Incrementally Verifiable Computation](https://iacr.org/archive/tcc2008/49480001/49480001.pdf) (IVC) or recursion techniques in order to recursively combine many proofs into one, and thus further reduce proof sizes and verification times. 
Additionally, minimizing the cost of reinstating users without major recomputation is a key challenge that needs addressing to make the schemes more adaptable and user-friendly. 
Finally, it is crucial to explore interoperability to ensure that anonymous blocklisting schemes can be seamlessly integrated with existing communication platforms and systems.
By tackling these challenges, we can move closer to using anonymous blocklisting in everyday digital communication.

 
 
[^1]: Technically this is the wrong terminology. The difference between a "proof" and an "argument" in cryptography lies in their soundness definition, which refers to the truthfulness of the protocol: if the statement is false, no Prover can convince a Verifier of the opposite. Proofs have statistical soundness (holds against an unbounded adversary), whereas arguments have only computational soundness (holds against a polynomially bounded adversary). For easier understanding, we can mislabel a SNARK, secure against bounded adversaries, as a "proof".

[^2]: In the world of Avatar, Aang (who is the Avatar) and Toph are part of a team trying to defend the Earth Kingdom against the Fire Nation, led by the Firelord and his son, Zuko. They end up in the city of Ba Sing Se (where Joo Dee resides) which has an authoritarian government refusing to acknowledge that a war is happening.

[^3]: While the described scheme has the same general mechanics as BLAC, it is presented in a simplified form that is closer to the SNARKBlock scheme for easier understanding. More details about the protocols can be found in the publications. 

[^4]: Some of the experiments include a buffer. This optimization aims to fix the problem when the blocklist might be updated during the Sync process, resulting in recomputation during the Attest process and thus added latency. So they use a buffer of smaller chunks at the end of the list and a separate HICIAP instance to process them, which increases the number of distinct proofs but reduces the overall attestation time.
