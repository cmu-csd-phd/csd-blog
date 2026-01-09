+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "Verified CNF Encodings"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2026-01-09

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Programming Languages"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
# Consider these similar to keywords specified for a research paper.
tags = ["SAT", "formal-methods", "lean", "correctness", "theorem-proving"]

[extra]
author = {name = "James Gallicchio", url = "https://gallicch.io/" }
# The committee specification is  a list of objects similar to the author.
committee = [
    {name = "Ruben Martins", url = "https://sat-group.github.io/ruben/"},
    {name = "Karl Crary", url = "https://www.cs.cmu.edu/~crary/"},
    {name = "Bernardo Subercaseaux", url = "https://bsubercaseaux.github.io/"}
]
+++

Boolean satisfiability, or SAT, is a classic computational problem:
given a Boolean formula, determine whether
there exists an assignment to the variables that satisfies the formula.
SAT is NP-complete, meaning all problems in the complexity class NP
can be (efficiently) translated into Boolean satisfiability problems.
We call these translations *SAT reductions*.

SAT reductions turn out to be quite useful for automated reasoning applications.
Circuit equivalence checking can be reduced to SAT,
which hardware companies use to verify the correctness of circuits.
SMT solvers, which are used for program verification and static analysis,
generate many SAT problems as part of their solving routine.
Reductions to SAT have even been used in pure mathematics,
performing combinatorial casework to solve previously unsolved conjectures.
Bernardo Subercaseaux recently wrote about SAT-for-mathematics
[on the CSD Blog](https://www.cs.cmu.edu/~csd-phd-blog/2025/sat-for-math/), go check it out!

For many automated reasoning applications, reductions to SAT are correctness-critical.
A mistake in the reduction can lead a user
to believe incorrect claims about the original problem domain.
As an example, suppose a hardware company wants to use SAT for circuit equivalence.
The hardware company designs a reduction \\(R\\) which takes two circuits and returns a Boolean formula.
They even write a pen-and-paper proof that this formula
meaningfully captures the circuit equivalence problem:

> **Theorem.** For all circuits \\(C_1, C_2\\), the formula \\(R(C_1, C_2)\\)
> is unsatisfiable if and only if \\(C_1 \equiv C_2\\).

*Why unsatisfiable?*
We want to ensure \\(C_1\\) and \\(C_2\\) behave the same on *all possible inputs*.
So, \\(R\\) returns a formula which is satisfied by any input where \\(C_1\\) and \\(C_2\\) behave differently.
Then, if the formula is unsatisfiable (every input fails to satisfy),
we know the circuits behave the same on every input.

The hardware company implements the reduction as a computer program,
and uses a general purpose SAT solver to compute whether the resulting formulas are satisfiable or not.
It works well, and they start using it as part of their circuit design process.
But, alas! their reduction implementation has a very small bug,
and occasionally produces an unsatisfiable formula for non-equivalent circuits.
This bug leads the company to think their broken circuitry is correct,
and by the time the mistake is discovered, it has become quite expensive to correct!

SAT solvers, as a black box for solving SAT problems, are remarkably trustworthy.
Modern SAT solvers produce *certificates of unsatisfiability*,
and those certificates are checked by formally verified software,
essentially ruling out any possibility that SAT solvers give wrong results.
Yet, as in our story above,
this remarkable trustworthiness can be completely undermined
before a SAT solver even comes into the picture.
**How do we expand the circle of trust beyond SAT solvers, to also encompass SAT *reductions*?**

SAT reductions are quite diverse and varied,
so answering this question is well beyond the scope of a single blog post.
However, most SAT reductions include a step called **CNF encoding**.
This is what we will focus on today.
We are going to learn what CNF encodings are,
go through examples of CNF encodings,
and discuss what "correctness" means for CNF encodings.
Then, we'll introduce `trestle`, a Lean 4 library
being developed by the author and collaborators,
and briefly examine how this library enables users
to write and verify the correctness of CNF encodings.


## SAT Definitions

First let's quickly review some key definitions from the SAT world.
A Boolean formula \\(F\\) is an *expression* built from the usual Boolean operators,
as well as Boolean-valued variables labeled by some set \\(V\\).
A *truth assignment* \\(\tau\\) maps the unknowns \\(V\\) to truth values \\(\\{\top, \bot\\}\\).
Given a truth assignment,
we can *evaluate* a formula to a truth value \\(\tau(F) \in \\{\top, \bot\\}\\)
using the standard reduction rules.
We say an assignment *satisfies* a formula, written \\(\tau \vDash F\\),
when \\(\tau(F) = \top\\).

Conjunctive normal form (CNF) describes a restricted class of Boolean formulas.
*Literals* \\(\ell\\) consist of either a variable or the negation of a variable.
*Clauses* \\(C\\) are a disjunction of literals,
and a *formula* \\(F\\) is a conjunction of clauses.

> **Definition.** *(Conjunctive Normal Form)*
> 
> \\[x \in V\\]
> \\[\ell ::= x \vert \overline{x}\\]
> \\[C ::= \bigvee_i \ell_i\\]
> \\[F ::= \bigwedge_i C_i\\]

Anywhere that I say "SAT" in this blog post, I mean CNF-SAT,
i.e. the computational problem of determining the satisfiability of *CNF formulas*.
This exclusive focus on CNF formulas happened for many reasons.
The data of a CNF formula is a list of clauses,
and the data of a clause is a list of literals.
SAT tools take advantage of this "list of lists of literals" representation
to store and manipulate CNF formulas efficiently.
Other reasons to work with CNFs will not be relevant here,
but curious readers should look into
the Tseitin transform, resolution proofs, and conflict-driven clause learning
(*Handbook of Satisfiability*[^handbook] 2.2.2, 3.2.1, and 3.6, respectively).

One more note:
when designing a reduction, the variables \\(V\\) will generally have some significance in the original problem domain.
For instance with the circuit equivalence problem, the variables might represent whether a wire is high or low.
But to a SAT solver, the elements of \\(V\\) are meaningless labels.
Any structure in \\(V\\) is ignored.
So to simplify the interface to SAT tools,
the SAT community standardized around *integer labels* for variables,
essentially fixing \\(V = \mathbb{N}^+\\).
We will see that this choice leads to some tension between theory and implementation.
When humans describe a formula on paper, we use descriptive, meaningful labels for the variables.
Yet in the implementation, we must map those descriptive labels to elements of \\(\mathbb{N}^+\\).


## CNF Encodings

Reductions to SAT frequently use constraints which are *not* expressed as CNF formulas.
Since SAT solvers operate exclusively on CNF formulas,
at some point those constraints must be translated into CNF formulas.
CNF encoding refers to that translation, from arbitrary constraints into CNF formulas.
Crucially, CNF encoding happens *after* we already have a set of Boolean variables \\(V\\) in mind.
The constraints are in terms of Boolean variables, just not expressed in conjunctive normal form.

Let's give an example.
The at-most-one constraint, \\(\text{AMO}_L\\), is a classic and common Boolean constraint.
Given a list of literals \\(L\\), it requires that *at most* one literal from \\(L\\) evaluates to true.
We express constraints formally as a predicate on assignments.

> **Definition.** *(At-Most-One Constraint)*<br/><br/>
> 
> Let \\(\\#(\cdot)\\) be defined by \\( \\#(\top) = 1 \\) and \\( \\#(\bot) = 0 \\).
> Then the at-most-one constraint is defined by
> \\[ \text{AMO}_L(\tau) \quad\iff\quad \sum _{\ell \in L} \\#(\tau(\ell)) \le 1 \\]
> 
> The sum counts how many literals in \\(L\\) are satisfied by \\(\tau\\).
> Thus, this accepts all assignments for which the number of satisfied literals is **at most one**.

Notice that, while it is a constraint over Boolean variables,
\\(\text{AMO}_L\\) is not written as a conjunctive normal form formula.
If we want to use this constraint in a (CNF-)SAT context,
we must *encode* it into a CNF formula.

The simplest way to encode the AMO constraint is called the **pairwise encoding**.
For every pair of literals in \\(L\\), one of them must be false:
\\[ \text{Pairwise}(L) \triangleq \bigwedge_{[\ell_1, \ell_2] \sqsubseteq L} (\overline{\ell_1} \lor \overline{\ell_2}) \\]
This is a formula in conjunctive normal form, as desired.
The formula is also satisfied by the same assignments as \\(\text{AMO}_L\\):
if an assignment satisfies two or more literals in the list,
then some clause (and therefore the whole formula) will be falsified.
Note the number of clauses is quadratic in the size of \\(L\\),
because there are \\(O(|L|^2)\\) pairs of literals.
Can we encode AMO in fewer clauses?

Suppose we split the list of literals into two sub-lists: \\(L = A, B\\).
Let \\(t\\) be a fresh Boolean variable (i.e. it is not used anywhere else in our formula),
and consider the conjunction of constraints
\\[ \text{AMO} _{A, \overline{t}} \land \text{AMO} _{t, B} \\]
Think of \\(t\\) as a switch that chooses whether to allow a true literal in \\(A\\) or in \\(B\\).
Consider the case where \\(t\\) is assigned true.
The left half of our split constraint becomes equivalent to \\(\text{AMO}_A\\),
since the \\(\overline{t}\\) literal is falsified.
But in right half, since \\(t\\) is satisfied, *all* of the literals in \\(B\\) must be falsified.
The case where \\(t\\) is assigned false is similar:
at most one of the literals in \\(B\\) can be true, while all of the literals in \\(A\\) must be false.
Since \\(t\\) is otherwise unconstrained,
this split constraint still essentially encodes an at-most-one constraint over the original list of literals \\(L\\).

The **cut-4** encoding uses this splitting lemma
to repeatedly cut the AMO constraint into groups of 4 literals.
Those small AMO constraints are then encoded with the pairwise encoding.
\\[ \text{Cut4}(\ell _1, \ell _2, \dots, \ell _{10}) \triangleq
    \text{Pairwise}(\ell _1, \ell _2, \ell _3, \overline{t_1}) \land
    \text{Pairwise}(t_1, \ell _4, \ell _5, \overline{t_2}) \land \\]
\\[
    \qquad\qquad\qquad\qquad\qquad \text{Pairwise}(t_2, \ell _6, \ell _7, \overline{t_3}) \land
    \text{Pairwise}(t_3, \ell _8, \ell _9, \ell _{10})
\\]
Again, this is a formula in conjunctive normal form,
and per the splitting lemma above, it is also equivalent to the \\(\text{AMO}_L\\) constraint.
What about the size of the formula?
There are \\(O(|L|)\\) pairwise encodings,
which each generate \\(O(1)\\) clauses,
giving a total of \\(O(|L|)\\) clauses --
we improved (asymptotically) on the pairwise encoding,
at the cost of adding \\(O(|L|)\\) fresh variables.

The pairwise and cut-4 encodings both express our original at-most-one constraint as a CNF formula, so why have both?
Experimentally, we find that SAT solvers perform differently on these encodings.
Sometimes the pairwise encoding is best, sometimes cut-4, sometimes other AMO encodings.[^joseph-thesis]
In general, adding auxiliary variables can make a CNF encoding more compact (fewer clauses),
and this compactness can both improve and worsen the performance of SAT solvers.
The tradeoff is an area of active research.[^ulc-reencode]
Regardless, CNF encodings must
**carefully manage where and how auxiliary variables are used**,
because this will significantly affect the performance of SAT solvers on the resulting formulas.


## Auxiliary Variables, Formally

Now we understand that CNF encodings sometimes introduce new variables ("auxiliary" variables)
in order to produce a more compact CNF formula.
While we are introducing new terminology,
let's call the variables that existed *before* CNF encoding (i.e. non-auxiliary variables)
the "problem" variables,
because they usually have a meaning in the original problem domain.
I think auxiliary variables are actually quite confusing,
so let's try to understand what exactly they are doing in a formula.

Consider some satisfying assignment \\(\tau\\) to a CNF formula \\(F\\).
The domain of \\(\tau\\) is the entire variable set \\(V\\);
the assignment gives a truth value to all the variables in the formula.
However, we can *truncate* an assignment, looking only at a subset of its full domain.

For example, we could truncate the full assignment to a smaller one \\(\sigma\\)
whose domain is just the problem variables in \\(F\\).
We can even generalize the \\(\tau \vDash F\\) notion to these partial assignments:
\\[ V_0 \subseteq V \qquad \qquad \sigma : V_0 \rightarrow \\{\top,\bot\\} \\]
\\[ \sigma \vDash^{V_0} F \quad \iff \quad
    \exists \tau : V \rightarrow \\{\top,\bot\\}, \\; \sigma \subseteq \tau \\; \land \\; \tau \vDash F \\]
Intuitively, if \\(\sigma\\) can be *extended* to a full assignment \\(\tau\\) satisfying \\(F\\),
then \\(\sigma\\) in some sense satisfies \\(F\\).
An equivalent interpretation is that we are existentially quantifying away
those variables not in \\(V_0\\):
\\[ \sigma \vDash \exists x_{105} \\; x_{106} \\; x_{107} \dots, \\;\\; F \\]
Either way, these truncated assignments reveal that auxiliary variables
act like existentially quantified variables.

> **Key Idea.** Auxiliary variables are *existential quantifiers* which bind fresh variables.

CNF encodings are like expressions in some formal language.
Auxiliary variables are *bound* variables, bound at existential quantifiers.
Problem variables, then, are akin to *free* (unbound) variables.
The Boolean assignments \\(\tau\\) are akin to an environment,
providing valuations for the free variables in an expression.

Why does this matter?
Well, if we were to treat auxiliary variables as globally scoped,
equivalent to problem variables,
then we would have great difficulty discussing the relationship
between the pairwise and cut-4 encodings
because they do not have the same set of (problem + auxiliary) variables.
It is comparing apples to oranges.
Instead, if we view auxiliary variables as *bound* variables,
then we can compare any two encodings which have the same set of unbound problem variables.
The pairwise and cut-4 encodings have the same set of problem variables,
which come from the provided list of literals.
We can discuss the satisfying assignments for each encoding,
where the domain for those assignments is only the problem variables,
and therefore is the same in both encodings.


## Verifying Encoding Programs

So far we have been treating CNF encodings as these mathematical transformations
on purely logical formulas.
In reality, we want to be verifying encodings as *programs*,
programs which output a CNF formula in the standard format expected by SAT solvers.
Remember, SAT solvers expect variables (both problem and auxiliary)
to be labeled with natural number IDs.
Encoding programs must *allocate* those IDs to variables correctly.
Simultaneously, we want to ensure the output formula matches some abstract specification.

The `trestle` library provides all of this functionality within a type called `EncCNF`.
This type helps us write any CNF encoding program in a clean (and *verifiable*) fashion.
Let's examine how the pairwise and cut-4 encodings are implemented with this `EncCNF` type.
Our library is written in Lean, which I do not expect most readers to be familiar with.
Try to focus solely on the control flow within these programs;
it should closely match the structure of the mathematical descriptions for each encoding.

```lean
def amoPairwise (lits : List (Literal V)) : EncCNF V Unit := do
  for _h : i in [ 0 : lits.length ] do
    for _h : j in [ i+1 : lits.length ] do
      addClause #[-lits[i], -lits[j]]

def amoCut4 (lits : List (Literal V)) : EncCNF V Unit := do
  if lits.length ≤ 4 then
    amoPairwise lits
  else
    -- Allocate one auxiliary variable
    withTemps Unit (do
      -- Take three literals from the front of the list
      let front := ( lits.take 3 ).map (LitVar.map Sum.inl)
      let back  := ( lits.drop 3 ).map (LitVar.map Sum.inl)
      -- tmp is the auxiliary variable we just allocated
      let tmp := Sum.inr ()
      -- pairwise encode this group of 4
      amoPairwise (front ++ [Literal.neg tmp])
      -- recursively encode the remainder
      amoCut4 ((Literal.pos tmp) :: back)
    )
```

I want to re-emphasize that these encoding programs are executable Lean code.
We can run them and output CNF formulas in the format expected by SAT solvers.
The fictional hardware company from the beginning of the blog post
lost a bunch of fictional money *because of a bug in one of these programs*.
We want to verify *these programs* are correct.

The definition of `EncCNF` is not particularly complicated.
The `EncCNF` type is implemented as a state monad.
The state includes a CNF formula (with natural number IDs for variables),
a mapping from variables `V` to natural number IDs,
and an allocator for obtaining fresh natural number IDs.

The `addClause` operation, for example,
takes an argument as a clause with variables in `V`.
It then translates the clause using the map from `V` to natural number IDs,
and adds this translated clause to the CNF.
The `withTemps` operation does not touch the CNF, but does modify the variable mapping.
It allocates a new variable and adds it to the variable map.
Within the body of a `withTemps`,
we have access to this new auxiliary.
But once the body of that `withTemps` is done,
the variable map is reset to what it was before the `withTemps`,
and we lose access to that auxiliary.

The `amoCut4` program uses auxiliary variables.
However, thanks to our insight that auxiliary variables are bound by existential quantifiers,
we can still give specifications for these encodings in terms of their satisfying assignments on `V`.
Notice that the `EncCNF` type takes `V` as a parameter;
this is to indicate that `V` are the problem variables in our formula,
and that we will be specifying the encodings' correctness in terms of assignments on `V`.
In particular, both of the AMO implementations encode
the at-most-one constraint defined in terms of counting satisfied literals:

```lean
theorem amoPairwise.correct :
    (amoPairwise lits).encodesProp (atMost 1 lits) :=
  sorry -- an easy proof

theorem amoCut4.correct :
    (amoCut4 lits).encodesProp (atMost 1 lits) :=
  sorry -- a less easy proof
```

The `encodesProp` relation is a bit tricky, both to define and to prove.
I am going to gloss over its definition to instead discuss how `trestle`
makes it easier to prove these `encodesProp` relationships.
In short, we use compositional reasoning.
We give a specification for each of the building blocks that make up these encoding programs,
and prove the `encodesProp` relation for each of those building blocks.
Then, we can build a specification and proof for larger programs
by composing these building blocks.

For example, the program `addClause C` is given the spec \\(\tau \vDash C\\).
Sequential composition of programs `E1 ; E2` gets the spec \\(P _1(\tau) \land P _2(\tau)\\),
where \\(P_1\\) and \\(P_2\\) are the specs for `E1` and `E2`.
For loops correspond to \\(\forall\\) quantification,
and `withTemps` auxiliary allocation corresponds to \\(\exists\\) quantification.
These are the building blocks from which we constructed the encoding programs above.
The `trestle` library includes (difficult) proofs that each component matches its spec.
Once each component is verified, though,
we get specs and proofs for larger programs for free.
In essence, we *simultaneously* construct an encoding program,
a spec for that encoding, and a proof that the program correctly encodes the spec.

The generated spec is usually not the one we ultimately want.
However, it is a *predicate in first order logic* rather than a messy stateful program.
We can prove the generated spec is equivalent to our desired spec,
using extremely standard first order logical reasoning.
The result is that users of `trestle` can verify the correctness of an encoding program,
without ever reasoning about the encoding *as a program*.
Users get precise control over the CNF output of their encoding,
*and* a straightforward methodology for proving that program matches an abstract specification.


## Related Work

Prior work on formally verifying SAT reductions has mostly
sidestepped the problem of managing auxiliary variables.
SAT reductions were formally verified for the Pythagorean triples problem[^pythag-trip-verif]
and the "Happy Ending" problem[^happy-end-verif].
In both of those results, the CNF encodings are straightforward and do not use auxiliary variables.
A SAT reduction was also formally verified for the "Empty Hexagon" problem[^empty-hex-verif],
and that reduction uses a more complex encoding.
The authors in that work use a verified Tseitin transformation from general Boolean formulas to CNF formulas.
This transformation introduces auxiliary variables,
but it does not give the encoding program precise control over how those auxiliaries are used.
In essence, we lose some expressivity compared to unverified CNF encodings.

Lastly, in recent but unpublished work,
I developed an end-to-end verification of the resolution of Keller's conjecture.
This is a theorem in combinatorial geometry, proven via a SAT reduction.[^res-keller-conj]
I used the `trestle` encoding utilities to write and verify the CNF encoding in that reduction.
The encoding made careful use of auxiliary variables,
and also used at-most-one encodings as a subcomponent.
Nonetheless, the encoding program was one of the easiest parts of the reduction to verify correct.
The `trestle` utilities automated all the challenging aspects of CNF encoding verification.


## Concluding Remarks

**For people interested in verifying CNF encodings:**
The most important insight from our work is
to treat auxiliary variables in CNF encodings as existentially quantified bound variables.
This approach enables *compositional reasoning* about encodings,
making it more practical to formally verify larger and more complex encodings.

**For everyone else:** My biggest takeaway from working on `trestle`
is that formal verification drives the creation of better programming tools.
The `trestle` encodings still have some rough edges,
and yet I prefer to write CNF encodings with `trestle` rather than C or Python.
Thanks to our handling of auxiliary variables,
I never have to think about freshness or name collisions.
Thanks to the compositional reasoning properties of `EncCNF`,
I can easily write and call subcomponents without thinking about what state to pass around.
To me, it is incredibly cool that
the features we developed for the purpose of formal verification
are still helpful even when not formally verifying anything!

## Acknowledgements

The research presented here is joint work with a number of collaborators,
primarily [Cayden Codel](https://crcodel.com/) and [Wojciech Nawrocki](https://voidma.in/).

I want to thank my Writing Skills committee,
Ruben Martins, Karl Crary, and Bernardo Subercaseaux,
for their suggestions and feedback on this post.
I also want to thank Cayden Codel, Thea Brick,
and others for their feedback on early drafts.

## References

[^handbook]: A. Biere, M. Heule, H. Van Maaren, and T. Walsh, Eds., Handbook of Satisfiability: Second Edition, vol. 336. in Frontiers in Artificial Intelligence and Applications, vol. 336. IOS Press, 2021. doi: 10.3233/FAIA336.
<br/><br/>

[^joseph-thesis]: J. E. Reeves, “Cardinality Constraints in Boolean Satisfiability Solving,” PhD Thesis, Carnegie Mellon University, Pittsburgh, PA, 2025. \[Online\]. Available: https://www.cs.cmu.edu/~jereeves/research/jereeves_phd_csd_2025.pdf
<br/><br/>

[^ulc-reencode]: A. Sheng, J. E. Reeves, and M. J. H. Heule, “Reencoding Unique Literal Clauses,” LIPIcs, Volume 341, SAT 2025, vol. 341, p. 29:1-29:21, 2025, doi: 10.4230/LIPICS.SAT.2025.29.
<br/><br/>

[^pythag-trip-verif]: L. Cruz-Filipe, J. Marques-Silva, and P. Schneider-Kamp, “Formally Verifying the Solution to the Boolean Pythagorean Triples Problem,” J Autom Reasoning, vol. 63, no. 3, pp. 695–722, Oct. 2019, doi: 10.1007/s10817-018-9490-4.
<br/><br/>

[^happy-end-verif]: F. Marić, “Fast Formal Proof of the Erdős–Szekeres Conjecture for Convex Polygons with at Most 6 Points,” J Autom Reasoning, vol. 62, no. 3, pp. 301–329, Mar. 2019, doi: 10.1007/s10817-017-9423-7.
<br/><br/>

[^empty-hex-verif]: B. Subercaseaux, W. Nawrocki, J. Gallicchio, C. Codel, M. Carneiro, and M. J. H. Heule, “Formal Verification of the Empty Hexagon Number,” Mar. 26, 2024, arXiv: arXiv:2403.17370. doi: 10.48550/arXiv.2403.17370.
<br/><br/>

[^res-keller-conj]: J. Brakensiek, M. Heule, J. Mackey, and D. Narváez, “The Resolution of Keller’s Conjecture,” Apr. 17, 2023, arXiv: arXiv:1910.03740. doi: 10.48550/arXiv.1910.03740.
<br/><br/>

[^fmcad-verif-enc]: C. Codel, J. Avigad, and M. Heule, “Verified Encodings for SAT Solvers,” Oct. 2023, TU Wien. doi: 10.34727/2023/ISBN.978-3-85448-060-0_22.
