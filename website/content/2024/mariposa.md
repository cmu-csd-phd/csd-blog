+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "Mariposa: the Butterfly Effect in SMT-based Program Verification"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2024-06-08

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Programming Languages"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
# Consider these similar to keywords specified for a research paper.
tags = ["SMT solver", "program verification"]

[extra]
# For the author field, you can decide to not have a url.
# If so, simply replace the set of author fields with the name string.
# For example:
#   author = "Harry Bovik"
# However, adding a URL is strongly preferred
author = {name = "Yi Zhou", url = "https://yizhou7.github.io/" }
# The committee specification is simply a list of strings.
# However, you can also make an object with fields like in the author.
committee = [
    "Committee Member 1's Full Name",
    "Committee Member 2's Full Name",
    {name = "Harry Q. Bovik", url = "http://www.cs.cmu.edu/~bovik/"},
]
+++


The Satisfiability Modulo Theories (SMT) solver is a
powerful tool for automated reasoning. For those who are
unfamiliar, you may think of an SMT solver as a "bot" that
answers logical or mathematical questions. For example, I
can ask if the following statement holds: 

$$ \exists  a, b, c \in Z  | 
3a^{2} -2ab -b^2c = 7 $$

Using the SMT-standard format, I can express the question as
the following query. The translation is  hopefully
straightforward: the `declare-fun` command creates a 0-arity
function (i.e., a variable), the `assert` command states the
formula as a constraint, and the `check-sat` command asks
the bot to check if the formula holds (is satisfiable) or
not. A slight quirk is that the expressions are in prefix
form, where each operator comes before its operand(s).

```
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(assert (exists ((a Int) (b Int) (c Int))
    (=
        (+ (* 3 a a) (* -2 a b) (* -1 b (* c b)))
        7
    )
))
(check-sat)
```
If the bot responds with "Yes", that is good! The answer is
not so obvious to me at least. What's more, the bot provides
fairly high assurance about its responses. I will refrain
from going into the details, but its answer is justified by
**precise mathematical reasoning**. For example, in this
case the bot can also provide a solution, `a = 1, b = 2, c =
-2`, which serves as a checkable witness to the "Yes"
answer.

However, the robot is not perfect. Suppose that I slightly
tweak the formula and ask again:

<!-- $ \exists \, e, f, g \in Z \, | \,
3e^{2} -2ef -e^2g = 7 $
 -->

```
(declare-fun e () Int)
(declare-fun f () Int)
(declare-fun g () Int)
(assert (exists ((e Int) (f Int) (g Int))
    (=
        (+ (* 3 e e) (* -2 e f) (* -1 f (* g f)))
        7
    )
))
(check-sat)
```

This time, the following may happen: the robot gives up,
saying "I don't know" to this new query. Understandably,
this may seem puzzling. As you might have noticed, the two
queries are essentially the same, just with different
variable names. Why would the bot give different responses?
Is it even a legitimate move for it to give up?

Before you get mad at the bot, let me explain. As mentioned
earlier, the SMT solver sticks to precise mathematical
reasoning, meaning that it should not give any bogus answer.
Consequently, when it sees hard questions, it is allowed to
give up. How hard? Well, some questions can be NP-hard! In
fact, the above queries pertain to Diophantine equations,
which are undecidable in general. Therefore, no program can
answer all such questions correctly. The poor bot has to
resort to heuristics, which may not be robust against
superficial modifications to the input query.

<!-- ### Instability of SMT Solving -->

What we have observed is the phenomenon of **SMT
instability**, where trivial changes to the input query may
incur large performance variations (or even different
responses) from the solver. While there are many
applications of SMT solvers, in this blog post, I will focus
on instability in **SMT-based program verification**, where
we ask the solver to prove programs correct. More
concretely, instability manifests as a butterfly effect:
even tiny, superficial changes in the program may lead to
noticeable changes in the proof performance or even create
spurious verification failures.

<!-- spurious proof failures, where a previously proven program
may be (wrongfully) rejected after trivial changes to the
source code.  -->

# Instability in SMT-based Program Verification

If you are already familiar with program verification using
SMT solvers, please feel free to skip this section.
Otherwise, please allow me to briefly explain why program
verification is useful, how SMT solvers can help with
verification, and why instability comes up as a concern.

As programmers, we often make informal claims about our
software. For example, I might claim that a filesystem is
crash-safe or an encryption software is secure, etc. However, as
myself can also testify, these claims can sometimes be
unfounded or even straight-up wrong. Fortunately, formal
verification offers a path to move beyond informal claims.

Formal verification uses proofs to show that the code meets
its specification. In comparison to testing, formal
verification offers a higher level of assurance, since it
reasons about the program's behavior for _all possible
inputs_, not just the ones in the test cases. In a
more-or-less [standard
algorithm](https://en.wikipedia.org/wiki/Predicate_transformer_semantics),
program properties can be encoded as logical statements,
often called the verification conditions (VCs). Essentially, the
task of formal verification is to prove that the VCs hold.

As you might have gathered from the previous example, the
SMT solver can reason about pretty complex logical
statements. Hence, a natural resort to prove the VCs is
through an SMT solver. In this way, the solver enables a
high degree of automation, allowing the developer to skip
many tedious proof steps. This methodology has made
verification of complex software systems a reality.

However, SMT-based automation also introduces the problem of
instability. Verified software, similar to regular software,
has an iterative development process. As we make incremental
changes to the code, corresponding queries also change
constantly. Even seemingly trivial changes, such as renaming
a variable would create a different query. As we have
discussed, the solver may not respond consistently to these
changes. 

# Detecting Instability with Mariposa

Now that we have a basic understanding of the problem, let's
try to systematically quantify instability. I will introduce
the methodology used in Mariposa, a tool that we have built
for this exact propose. In this blog post, I will stick to
the key intuitions. For a more detailed discussion, I
encourage you to check out the Mariposa paper. At a high
level, given a query \\( q \\) and an SMT solver \\( s \\),
Mariposa answers the question: 

> Is the query-solver pair \\((q, s)\\) stable?

<p></p>

Intuitively, instability means that the performance of \\( s
\\) diverges when we apply seemingly irrelevant mutations to
\\( q \\). Mariposa detects instability by generating a set
of mutated queries and evaluating the performance of \\( s
\\) on each mutant. In this section, I will explain the
mutations used, and how Mariposa decides the stability
status of the query-solver pair.

## What Mutations to Use?

In Mariposa, a mutation method needs to preserve the
semantic meaning and the syntactic structures of a query.
More precisely, the original query \\( q \\) and its mutant
\\( q' \\) need to be  both semantically equivalent and
syntactically isomorphic. 
<!-- it seems reasonable to expect similar performance from
the solver on both queries. -->

* **Semantic Equivalence**. \\( q \\) and \\( q' \\) are semantically equivalent
when there is a bijection between the set of proofs for \\( q \\)
and those for \\( q' \\) . In other words, a proof of \\( q \\) can be
transformed into a proof of \\( q' \\) , and vice versa. 

* **Syntactic Isomorphism**. \\( q \\) and \\( q' \\)  are
syntactically isomorphic if there exists a bijection between
the symbols (e.g., variables) and commands (e.g.,
`assert`). In other words, each symbol or command in \\( q \\)  has
a counterpart in \\( q' \\), and vice versa. 

For our concrete experiments, we are interested in mutations
that also correspond to common development practices.
Specifically, we consider the following three mutation
methods:

* **Assertion Shuffling**. Reordering of source-level lemmas
or methods is a common practice when developing verified
software. Such reordering roughly corresponds to shuffling
the order of commands in the generated SMT query.
Specifically, SMT queries introduce constraints using the
`assert` command. Shuffling the order in which the
constraints are declared guarantees syntactic isomorphism.
Further, the order within a local context is irrelevant to
the query’s semantics.

* **Symbol Renaming**. It is common to rename source-level
methods, types, or variables, which roughly corresponds to
α-renaming the symbols in the SMT queries. Renaming
preserves semantic equivalence and syntactic isomorphism, as
long as the symbol names are used consistently.

* **Randomness Reseeding**. SMT solvers optionally take as
input a random seed, which is used in some of their
non-deterministic choices. Changing the seed has no effect
on the query’s semantics but is known to affect the solver’s
performance. While technically not a mutation, reseeding has
been used as a proxy for measuring instability, which is a
reason why we have included it here.

<!-- Historically, some verification tools have
attempted to use reseeding to measure instability: Dafny and
F* have options to run the same query multiple times with
different random seeds and report the number of failures
encountered.
 -->

<!-- Let's consider an example. Suppose we have a query \\( q
\\) with \\( 100 \\) assertions. If we exhaustively apply
shuffling to \\( q \\), we obtain a set of mutated queries
\\( M_q \\), with \\(100! \approx 9 \times 10^{157}\\)
permutations of \\( q \\).  -->


## Stable or Not?

<!-- I will assume a single
mutation method, such as assertion shuffling, is used. 
 -->
**Mutant Success Rate**. Intuitively, whether a query-solver
pair \\( (q, s) \\) is stable depends on how the mutants
perform. A natural performance metric is the success rate of
\\( s \\) over mutants of \\( q \\), i.e., the percentage of
the mutants that are verified by \\( s \\). The success
rate, denote by \\(r\\), ranges from \\(0\\% \\) to
\\(100\\% \\). Since it reflects performance consistency.
Mariposa introduces four stability categories based on the
\\(r\\) value. 


 <!-- A low \\(r\\) indicates
consistently poor results; a high \\(r\\) indicates
consistently good results; and a moderate \\(r\\) indicates
inconsistent results, i.e., instability.
 -->
<!-- The scheme
includes two additional parameters: \\(r_{solvable}\\)  and
r stable , which correspond respectively to the lower and
upper bounds of the success rate range for unstable queries. -->

* **unsolvable**. A low \\(r \\) value \\( (\approx 0\\%)
  \\) indicates that \\( q \\) is too difficult for\\( s
\\). For example, if \\( s \\) gives up and returns unknown
for all members of \\( M_q \\), we may conclude that \\( s
\\) is unable to solve \\( q \\) or any version of it.
* **stable**. A high \\(r\\) value \\( (\approx 100\\%) \\)
  implies stability, meaning \\( s \\) verifies \\( M_q \\)
consistently.
* **unstable**. A moderate \\(r\\) value \\( ( 0 \\% \ll  r
  \ll 100  \\%) \\) indicates that \\( s \\) cannot
consistently find a proof in the presence of mutations to
\\( q \\).
* **inconclusive**. Statistical tests do not result in
enough confidence to draw a conclusion.

<!-- • unsolvable. Q is too difficult for solver S (r <
r solvable ). For example, if S gives up and returns
unknown for all members of M Q , we may conclude
that S is unable to solve Q or any version of it.
• unstable. S cannot consistently find a proof in the
presence of mutations to Q (r solvable ≤ r < r stable ).
• stable: S proves M Q consistently (r ≥ r stable ).
• inconclusive: statistical tests do not result in
enough confidence to draw a conclusion. -->



# Measuring Instability in the Wild

#### Benchmarks

# Should We Blame the Solver?

# Should We Blame the Query?

