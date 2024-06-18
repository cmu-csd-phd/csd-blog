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

If you are already familiar with this background topic,
please feel free to skip this section. Otherwise, please
allow me to briefly explain why program verification is
useful, how SMT solvers can help with verification, and why
instability comes up as a concern.

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
try to quantify instability systematically. I will introduce
the methodology used in Mariposa, a tool that we have built
for this exact propose. In this blog post, I will stick to
the key intuitions and elide many of the details. For a more
thorough discussion, I encourage you to check out the
Mariposa paper. At a high level, given a query \\( q \\) and
an SMT solver \\( s \\), Mariposa answers the question: 

> Is the query-solver pair \\((q, s)\\) stable?

<p></p>

Intuitively, instability means that the performance of \\( s
\\) diverges when we apply seemingly irrelevant mutations to
\\( q \\). Mariposa detects instability by generating a set
of mutated queries and evaluating the performance of \\( s
\\) on each mutant. In this section, I will explain what
mutations are used, and how Mariposa decides the stability
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
Further, the order in which the constraint is introduced 
does not change the query’s semantics.

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


## Is it Stable or Not?

Whether a query-solver pair \\( (q, s) \\) is stable or not
depends on how the mutants perform. A natural performance
metric is therefore the **Mutant Success Rate**: the
percentage of \\( q\\)'s mutants that are verified by \\( s \\).
The success rate, denoted by \\(r\\), reflects performance
consistency. Mariposa further introduces four stability
categories based on the \\(r\\) value. 

<!-- The scheme
includes two additional parameters: \\(r_{solvable}\\)  and
r stable , which correspond respectively to the lower and
upper bounds of the success rate range for unstable queries. -->

* **Unsolvable**. A low \\(r \\) value \\( (\approx 0\\%)
  \\) indicates that the performance is consistently poor.
For example, if \\( s \\) gives up and returns unknown for
all mutants, we may conclude that \\( q \\) is simply too
difficult for \\( s \\). 
* **Unstable**. A moderate \\(r\\) value \\( ( 0 \\% \ll  r
  \ll 100  \\%) \\) indicates that \\( s \\) cannot
consistently find a proof in the presence of mutations to
\\( q \\), meaning that we have observed instability.
* **Stable**. A high \\(r\\) value \\( (\approx 100\\%) \\)
 means \\( s \\)  the performance is consistently well,
 which is the ideal case.
* **Inconclusive**. This category is needed due to a
technicality that is not super important for our discussion
here. In short, because Mariposa uses random sampling to
estimate the success rate, sometimes statistical tests do
not result in enough confidence to place \\( (q, s) \\) in
any of the previous three categories.

# Measuring Instability in the Wild

So far we have discussed Mariposa's methodology to detect
and quantify SMT-based proof instability. How much
instability is there in practice? Well, let me share some
experimental results on existing program verification
projects.

## Projects and Queries

The table below lists the projects we experimented. I will
refrain from going into the details of each project, but
generally speaking, (1) these are all verified system
software such as storage systems, boot loaders, and
hypervisors. (2) they all involve non-trivial engineering
effort, creating a considerable number of SMT queries. (3)
they are all published at top venues, with source code and
verification artifacts available online. 
<!-- One thing I would like to point
out is that the artifact solver, i.e., the SMT solver used
in the verification process, are all quite old.  -->

| Project Name  | Source Line Count   | Query Count | Artifact Solver |
|:------------- | -----------:| -----------:|:-----------:|
| Komodo\\(_D \\)     | 26K        |  2,054 | Z3 4.5.0 |
| Komodo\\(_S \\)     | 4K         |  773   | Z3 4.2.2 |
| VeriBetrKV\\(_D \\) | 44K        |  5,325 | Z3 4.6.0 |
| VeriBetrKV\\(_L \\) | 49K        |  5,600 | Z3 4.8.5 |
| Dice\\(_F^⋆\\)      | 25K        |  1,536 | Z3 4.8.5 |
| vWasm\\(_F \\)     | 15K         |  1,755 | Z3 4.8.5 |

<!-- | Project Name  | Source Line Count   | Query Count |
|:------------- | -----------:| -----------:|
| Komodo\\(_D \\)     | 26K        |  2,054 |
| Komodo\\(_S \\)     | 4K         |  773   |
| VeriBetrKV\\(_D \\) | 44K        |  5,325 |
| VeriBetrKV\\(_L \\) | 49K        |  5,600 |
| Dice\\(_F^⋆\\)      | 25K        |  1,536 |
| vWasm\\(_F \\)     | 15K         |  1,755 | -->


## How Much Instability?

For our experiments, we focus on the Z3 SMT solver, with
which the projects were developed. We are interested in both
the current and historical status of SMT stability.
Therefore, in addition to the latest Z3 solver (version
4.12.1, as of the work), we include seven legacy versions of
Z3, with the earliest released in
2015. In particular, for each project we include its
artifact solver, which is the version used in the project’s
artifact.

For each query-solver pair \\( (q, s) \\), we run Mariposa,
which outputs a stability category. In Figure 1, each
stacked bar shows the proportions of different categories in
a project-solver pair. Focusing on Z3 4.12.1 (the right-most
group), the unstable proportion is \\( 5.0\\% \\) in
Komodo\\(_D \\), and \\(2.6\\%\\) across all queries. This
might not seem like a significant number, but think of a
regular CI where \\(\sim 2\\%\\) of the test cases may fail
randomly: it would be a nightmare! Nevertheless, developers
have to bear with this in SMT-based verification. Many of
the authors have documented the frustration of dealing with
instability.

<!-- In all project-solver pairs, the majority of queries are
stable. However, a non-trivial amount of instability
persists as well.   -->

![The main experiment results from Mariposa.](./mariposa_exp.png)

<figcaption>Figure 1: Overall Stability Status. From bottom to top, each stacked bar shows the proportions of unsolvable (lightly shaded), unstable
(deeply shaded), and inconclusive (uncolored) queries. The remaining portion of the queries (stacking each bar to 100%), not shown, are
stable. The solver version used for each project’s artifact is marked with a star (⋆). </figcaption>
<br>

Now that we know instability is not a rare occurrence, the
next question is: what gives? Well, as we have discussed
previously, it is all fundamentally due to undecidability.
However, let's be a bit more specific about the causes.
First and foremost, instability is a property of both the
query and the solver. Therefore, the causes can also be
categorized as query-related and solver-related.

# What's Wrong with the Solver?

<!-- As we zoom out to the full picture, the projects exhibit
different historical trends. The unstable proportion of
vWasm\\(_F\\) and Komodo\\(_S\\) remain consistently small
across the solver versions.  On the other hand, some
projects seem "overfitted" to their artifact solver, in that
they become less stable with solver upgrades. Specifically,
Komodo\\(_D \\), VeriBetrKV\\(_D \\), and VeriBetrKV\\(_L
\\) show more instability in newer Z3 versions, with a
**noticeable gap** between Z3 4.8.5 and Z3 4.8.8.  -->

As you might have noticed in Figure 1 already, there is a
"gap" between Z3 4.8.5 and 4.8.8, where Komodo\\(_D \\),
VeriBetrKV\\(_D \\), and VeriBetrKV\\(_L \\) contain more
unstable queries with the newer solver. In other words,
certain queries used to be stable, but somehow become
unstable with the solver upgrade. Since the query did not
change, solver change must have been the cause to stability
regression. 

We perform further experiments to narrow down the Z3 git
commits that may have caused the increase in instability. In
the six experiment projects, 285 queries are stable under Z3
4.8.5 but unstable under Z3 4.8.8. For each query in this
set, we run git bisect (which calls Mariposa) to find the
commit to blame, i.e., where the query first becomes
unstable.

There are a total of 1,453 commits between the two versions,
among which we identify two most impactful commits. Out of
the 285 queries, 115 (40%) are blamed on commit `5177cc4`.
Another 77 (27%) of the queries are blamed on `1e770af`. The
remaining queries are dispersed across the other commits.

These two most significant commits are small and localized:
`5177cc4` has 2 changed files with 8 additions and 2
deletions; `1e770af` has only 1 changed file with 18
additions and 3 deletions. Both commits are related to the
order of flattened disjunctions. `1e770af`, the earlier of
the two, sorts the disjunctions, while `5177cc4` adds a new
term ordering for ASTs, which it uses to replace the
previous sorting order of disjunctions.

# What's Wrong with the Query?

The other side of the coin is the query itself. As it turns
out, 
