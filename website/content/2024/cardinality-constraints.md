+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "Encoding Cardinality Constraints in Automated Reasoning"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2024-11-26

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Programming Languages", "Artificial Intelligence"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
# Consider these similar to keywords specified for a research paper.
tags = ["automated reasoning", "satisfiability solving"]

[extra]
# For the author field, you can decide to not have a url.
# If so, simply replace the set of author fields with the name string.
# For example:
#   author = "Harry Bovik"
# However, adding a URL is strongly preferred
author = {name = "Joseph Reeves", url = "https://www.cs.cmu.edu/~jereeves/" }
# The committee specification is simply a list of strings.
# However, you can also make an object with fields like in the author.
committee = [
    {name = "Mor Harchol-Balter", url = "https://www.cs.cmu.edu/~harchol/"},
    {name = "Daniel Sleator", url = "https://www.cs.cmu.edu/~sleator/"},
    {name = "Noah Singer", url = "https://noahsinger.org/"} 
]
+++

<!-- {name = "Mor Harchol-Balter", url = "https://www.cs.cmu.edu/~harchol/"},
    {name = "Daniel Sleator", url = "https://www.cs.cmu.edu/~sleator/"},
    {name = "Noah Singer", url = "https://noahsinger.org/"} -->

<!-- After filling in the above "top-matter", as per instructions provided
in the `.md` file, you can write the main body of the blogpost here
onwards. Commonly used examples of syntax are shown below.

You can run `./local_server.sh` at the root of the repository to see
how the final blogpost looks in action. -->

**********

_Automated reasoning_ (AR) is a branch of artificial intelligence that applies various reasoning techniques to solve problems from mathematics and logic.
AR engines use clever optimizations and heuristics to solve typically intractable (e.g., NP-hard) problems. 
Before a problem can be solved with an AR engine it must first be _encoded_ as a list of constraints in some standardized input format. 
The choice of encoding can significantly impact an AR engine's performance.
For example, with some combinatorial principles choosing a good encoding will enable an AR engine to find a solution in a matter of seconds, but choosing a bad encoding will inhibit the AR engine's heuristics costing thousands of seconds of search before a solution is found.
In this post we will describe techniques for improving encodings for problems represented in Boolean (propositional) logic, giving some guidance for developing encodings that lead to faster solving times.

We have all practiced encoding problems at various levels of math.
Take for example this simple word problem:

>**Example 1.**
> $$$$
>  "Find an odd and an even integer that sum to 9."
> $$$$
>  An initial encoding might include the three constraints:
>
>  - \\(x + y = 9\\)
>  - \\(x\\) is even
>  - \\(y\\) is odd
>
>  We can take this a step further. If \\(x\\) is even then \\(x = 2k\\) for some integer \\(k\\), and if \\(y\\) is odd then \\(y = 2\ell + 1\\) for some integer \\(\ell\\), giving the new equation:
>
>  - \\(2k + (2\ell+1) = 9\\)
>
>  Now the problem is in a machine-understandable format, and we can send the linear equation to an AR engine which will produce some solution, e.g., \\(k = 2\\), \\(\ell = 2\\) meaning \\(x = 4\\) and \\(y = 5\\).

&nbsp;

We often think about and describe problems at a high-level, with abstract constraints (e.g., "\\(x\\) is even"). Encoding is the process of transforming a problem description into a specific format with variables, values, and operators (e.g., + and =), sometimes introducing new variables (e.g., \\(k\\) and \\(\ell\\)) to simplify the problem.
In practice, AR engines consistently solve problems across various domains including planning, cloud security, and software and hardware verification.
These problems may contain _thousands_ of variables and _millions_ of constraints. 


![Visualization of the workflow for solving a problem with automated reasoning. From left to right, the problem is passed to the encoder, then to the AR engine, then a solution is output.](./encode.png)
*Figure 1.* Solving a problem using automated reasoning.

The workflow for solving a problem with AR is shown in Figure 1.
Over the past two decades the performance of AR engines on diverse sets of problems has significantly improved (Biere et. al. 2023).
Much of this progress is due to the development of _inprocessing techniques_: rules for transforming problems during solving.
One of the most effective inprocessing techniques adds new variables that summarize parts of the problem to improve the AR engine's reasoning capabilities (Haberlandt et. al. 2023).
In our work, we study the importance of new variables but shift the focus from the AR engine (inprocessing) to the encoding. 
Specifically, we look at encodings for one of the most commonly occurring types of high-level constraints: cardinality constraints. 
We develop techniques that reorder variables within cardinality constraint encodings, finding these new encodings often improve the AR engine's performance such that it solves problems faster.
In this post, we use the game of Sudoku to (1) illustrate the basics of encodings in AR and specifically Boolean satisfiability, (2) describe two simple cardinality constraint encodings, and (3) show the importance of variable orderings in these encodings. We conclude with some experimental results showing the impact of our techniques.


## Representing Problems in Automated Reasoning

There is a general way to characterize the sorts of problems applicable to AR via **constraint satisfaction problems** (CSPs).

Each problem has three components:
1. A set of variables.
2. A set of possible values for each variable.
3. A set of constraints that must not be violated by a solution.

The goal of solving a CSP is to find an assignment of values to variables (a.k.a. a solution) that does not violate any of the constraints; or, to report that every possible assignment violates some constraint, meaning no solution exists.

![Example Sudoku puzzle with some values.](./sudoku1.png)
*Figure 2.* Example Sudoku puzzle.

Consider the game of [Sudoku](https://en.wikipedia.org/wiki/Sudoku) shown in Figure 2. (Note, the example in Figure 2 has fewer given values than a typical Sudoku puzzle for the purpose of simplifying its presentation.)
We might define the problem as:
1. A variable for each cell in the 9 x 9 grid.
2. Each variable can have a value from 1 to 9, and some variables' values are given.
3. No row, column, or inner 3 x 3 square may have a repeated value.


Now that we have written down the general components of the problem, to finish the encoding we must decide on a specific format.
Different AR engines have different input formats, and these formats determine how the problem is represented and what reasoning techniques the AR engine can use.
In Example 1, variables had integer values, and the constraints included the sum and multiplication operators with equivalence (=).
There exist AR engines called satisfiability modulo theories (SMT) solvers, that will solve problems in this format.
However, many problems are best solved by another sort of AR engine, Boolean satisfiability (SAT) solvers.

## Boolean Logic

The input format for SAT solvers is a formula (set of constraints) in Boolean (propositional) logic, restricting variables to the values true (1) and false (0). 
A variable \\(x\\) can occur in a constraint as a positive literal (\\(x\\)) or a negative literal (\\(\neg x\\)), where \\(\neg x\\) is true (1) if \\(x\\) is false, and false (0) if \\(x\\) is true.
Each constraint is a set of literals, and the constraint is satisfied, i.e., not violated, if at least one of the literals is true. This type of constraint is often referred to as a clause.

The _cardinality constraint_ \\(x_1 + x_2 + \dots + x_n \geq k \\) is satisfied when the sum of literals is greater than or equal to the bound \\(k\\). We can think of clauses as a special type of cardinality constraint with comparator \\(\geq\\) and bound 1, stating at least one of the literals is true. For example, the clause \\(x_1 \lor x_2 \lor \dots \lor x_n \\) can be thought of as the cardinality constraint \\(x_1 + x_2 + \dots + x_n \geq 1 \\).

So, given a problem as a set of cardinality constraints with arbitrary bounds, the cardinality constraints would need to be encoded into clauses before passing the problem to a SAT solver. We show an example of this in the following section, but first present some simple formulas with clauses.

> **Example 2.**
> $$ x + y + z \geq 1$$
> $$ \neg x + \neg z \geq 1$$
>
> A solution for the set of clauses above is \\(x=1,y=0,z=0\\).

> **Example 3.**
> $$ x + \neg z \geq 1$$
> $$ \neg x + \neg z \geq 1$$
> $$ z \geq 1$$
>
> There is no possible solution for the set of clauses above. To satisfy the third clause we must set \\(z = 1\\), then to satisfy the second clause we must set \\(x = 0\\), and these values violate the first clause.

&nbsp;

Returning to Sudoku, we must apply another layer of encoding to transform the problem into a formula in Boolean logic. The variables cannot have values from 1 to 9 but instead may only be true or false. We will address this by examining the specific cell \\(x\\) in the top left corner of the puzzle from Figure 3. 

![Example Sudoku puzzle with some values. A blue X variable is placed at the upper left-hand corner. The values that conflict with the X variable by sharing a row, column, or 3 by 3 square are highlighted red](./sudoku2.png)
*Figure 3.* Example Sudoku puzzle with the variable \\(x\\).

To represent the possible values (1-9) of \\(x\\), we will introduce 9 variables \\( x_1,x_2,\dots,x_9\\), where \\( x_i = 1\\) if \\(x\\) has value \\(i\\) and \\( x_i = 0\\) if \\(x\\) does not have value \\(i\\).
For example, the red values in Figure 3 cannot be held by \\(x\\) since they are in the same row or column, so \\( x_7 = x_8 = x_9 = 0\\).

We will add a clause stating that at least one of the \\(x_i\\) variables is true, meaning \\(x\\) has at least one value:

$$ x_1 + x_2 + \dots + x_9 \geq 1$$

Next, we need to ensure it is not possible that two \\(x_i\\) variables are true at the same time, e.g., \\( x_4 = x_5 = 1\\), because \\(x\\) cannot have two values simultaneously.
This requires the introduction of another constraint, an at-most-one (AMO) constraint:

$$ x_1 + x_2 + \dots + x_9 \leq 1$$

Remember, Boolean variables can be either true (1) or false (0), so this constraint says that at most one of the variables \\( x_i\\) are true; in other words, \\(x\\) cannot have two values simultaneously. Unfortunately, this AMO constraint is not a clause. We could switch the comparator, obtaining \\(\neg x_1 + \neg x_2 + \dots + \neg x_9 \geq 8\\) but a clause requires the bound to be 1. So, we must go one step further and encode the AMO constraint into clauses.

## Encoding Cardinality Constraints

There are multiple ways to encode an AMO constraint into clauses.
The simplest approach, sometimes called the naive or pairwise encoding, 
introduces clauses that say no pair of variables are true at the same time, e.g., \\(\neg x_1 + \neg x_2 \geq 1\\), for all pairs.

We can visualize the pairwise encoding as a connected graph, where each edge represents a clause between two variables saying they cannot both be true at once.

![Graph-based visualization of the pairwise AMO encoding on 9 variables x 1 through x 9. Each variable is connected by an edge, forming a complete graph on 9 nodes.](./graph2.png)
*Figure 4.* Graph-based visualization of the pairwise AMO encoding of $$ x_1 + x_2 + \dots + x_9 \leq 1$$

It is often the case that smaller encodings, measured by the number of clauses introduced, are better for solver performance (Asín et al. 2011). 
One way to reduce the size of an encoding is with the addition of new variables (a.k.a. encoding variables) that divide the constraint into subproblems.
We show an example of this using an instance of the commander encoding (Klieber and Kwon 2007) with three encoding variables \\(y_1,y_2,y_3\\):

$$ x_1 + x_2 + x_3 + \neg y_1 \leq 1$$
$$ x_4 + x_5 + x_6 + \neg y_2 \leq 1$$
$$ x_7 + x_8 + x_9 + \neg y_3 \leq 1$$
$$ y_1 + y_2 + y_3 \leq 1$$

In the encoding above, the encoding variables \\(y_1,y_2,y_3\\) split the original AMO constraint into three parts. Referring to the puzzle in Figure 3., if \\(x\\) has a value between 1 and 3, then \\(y_1\\) must be set to true. So, \\(y_1\\) summarizes the first third of the original AMO constraint.
Likewise, if \\(x\\) has a value between 4 and 6, then \\(y_2\\) must be set to true, and similarly for \\(y_3\\).
Finaly, we need the constraint stating at most one of \\(y_i\\) can be true.
Intuitively, at most one group (\\(y_i\\)) may be selected, and from that group at most one (\\(x_i\\)) value may be selected.
In general, the original cardinality constraint can be divided into arbitrarily sized groupings, 
but groupings of 3 are often used in practice to minimize both the number of encoding variables and number of clauses. By encoding one large AMO constraint as 4 smaller AMO constraints, the number of edges (clauses in the encoding) drops from 36 to 21.

![Graph-based visualization of the AMO encoding on 9 variables using 3 encoding variables. Three groups of x variables from 1 to 3, 4 to 6, and 7 to 9, are each connected to an encoding y variable. The y variables are then connected, creating a hierarchical structure.](./graph1.png)
*Figure 5.* Graph-based visualization of the commander AMO encoding of $$ x_1 + x_2 + \dots + x_9 \leq 1$$ using 3 encoding variables \\(y_1,y_2,y_3\\).

The benefits of smaller encodings are well-known. For example, encoding AMO constraints using smaller encodings can improve solving time significantly on unsatisfiable formulas (Reeves, Heule, and Bryant 2024).
However, there is more to a good encoding than its size.
In recent work we explored an alternative way to improve encodings by reordering variables within the constraint and therefore modifying the meaning of encoding variables without changing the size of the encoding.

## The Impact of Variable Ordering in Cardinality Constraints

There are many types of encodings for cardinality constraints, and they often introduce encoding variables that divide the cardinality constraint hierarchically into subproblems. One of the most  used cardinality constraint encodings is the totalizer (Bailleux and Boufkhad 2003), forming a tree-like structure with encoding variables at the internal nodes and problem variables (variables from the original constraint, e.g., \\(x_i\\)'s) at the leaves. At a high level, the encoding variables in the totalizer group problem variables together similar to the commander encoding from Figure 5. By changing the ordering of variables in the cardinality constraint we can change the groupings of variables in the encoding, thereby changing the meaning of encoding variables without affecting the overall meaning of the encoding or its size. Take for example a reordering of the AMO constraint on 9 variables:

$$ x_1 + x_3 + x_5 + x_2 + x_4 + x_6 + x_7 + x_8 + x_9 \leq 1$$

The visualization for encoding this cardinality constraint is shown in Figure 6. Note, this graph looks almost the same as in Figure 5 except the problem variables (\\(x_i\\)'s) have been reordered. This will result in the same encoding structure with respect to the number of clauses and encoding variables, with a permutation of variables within the clauses. With the reordering, \\(y_1\\) now summarizes \\(x_1,x_3,x_5\\) instead of \\(x_1,x_2,x_3\\). We will show how this small change can impact a solver's reasoning capabilities in an example below.

![Graph-based visualization of the AMO encoding on 9 variables using 3 encoding variables. Three groups of x variables  are each connected to an encoding y variable. The y variables are then connected, creating a hierarchical structure.](./graphs4.png)
*Figure 6.* Graph-based visualization of the AMO encoding on $$ x_1 + x_3 + x_5 + x_2 + x_4 + x_6 + x_7 + x_8 + x_9 \leq 1$$ using 3 encoding variables \\(y_1,y_2,y_3\\). Note, the difference from Figure 5 arises from a different ordering of the \\(x^i\\) variables in the cardinality constraint, yielding a different labelling of the nodes.


![Example Sudoku puzzle with some values. A blue X variable is placed at the upper left-hand corner. Green p, m, and n variables are placed in the first row, conflicting with the X variable.](./sudoku3.png)
*Figure 7.* Example Sudoku puzzle with three additional variables \\(p,m,n\\).

First, \\(x\\) cannot have the value 7,8, or 9, so \\( x_7 = x_8 = x_9 = 0\\), simplifying the AMO constraint for \\(x\\) to:

$$ x_1 + x_2 + x_3 + \neg y_1 \leq 1$$
$$ x_4 + x_5 + x_6 + \neg y_2 \leq 1$$
$$ y_1 + y_2 \leq 1$$

Looking at the puzzle in Figure 7, the variables \\(n,m,p\\) each can only have a value from the set 1,3, or 5. This is confirmed by examining the puzzle and considering the rows, columns, and squares for each of \\(n,m,p\\). Since \\(n,m,p\\) are all conflicting with \\(x\\) and each other, it must be true that \\(x\\) cannot have a value 1, 3, or 5, and must instead be either 2, 4, or 6. This fact is not easily learned with the given encoding for \\(x\\).

Let's consider the way \\(x_i\\) variables are grouped in the first two constraints of our encoding. Instead of the original grouping, we can use the grouping from Figure 7 and get:

$$ x_1 + x_3 + x_5 + \neg y_1 \leq 1$$
$$ x_2 + x_4 + x_6 + \neg y_2 \leq 1$$
$$ y_1 + y_2 \leq 1$$

The overall meaning is still the same, \\(x\\) can only have one value; but the meaning of the encoding variables has changed. Now, \\(y_1\\) is true when \\(x\\) has value 1,3, or 5; and \\(y_2\\) is true when \\(x\\) has value 2,4, or 6.

<!-- - carry out reasoning by contradiction. Assume something true, lead to conflict.

Again looking at the puzzle above. -->

Let's first assume the puzzle is fully encoded in Boolean logic, meaning that each of \\(n,m,p\\) have corresponding variables and constraints. Second, let's assume that a solver can propagate known values, for example, the solver can propagate \\(n \neq 9\\) since 9 is the same row as \\(n\\). With this new grouping of problem variables, a solver can carry out the following reasoning:

> Assume \\(y_1\\) from our second encoding is true.
> -  This makes \\(y_2\\) false, so \\(x\\) has a value 1,3, or 5.
> - The four variables \\(n,m,p\\) and \\(x\\) are on the same row and so all must have different values.
> -  We have three possible values 1,3, and 5 to assign to the four variables \\(n,m,p\\) and \\(x\\).
> - The solver reasons that this leads to a conflict, since each variable must have a unique value.
>
> Therefore, \\(y_1\\) must be false. This forces \\(y_2\\) to true since it is the only remaining encoding variable for \\(x\\), reducing the possible values of \\(x\\) to 2,4, or 6.

&nbsp;

<!-- Assume \\(y_1\\) from our second encoding was true, then \\(x\\) has value 1,3, or 5. This would eventually lead to a conflict since we cannot assign values to all of \\(n,m,p\\) if \\(x\\) also has a value from 1,3, or 5. In other words, we would have three possible values 1,3, and 5 to assign to the four variables \\(n,m,p\\) and \\(x\\), and since they are all on the same row this is impossible. Therefore, we can reason that \\(y_1\\) must be false, meaning \\(y_2\\) must be true since \\(x\\) must be assigned some value. This reduces the possible values of \\(x\\) to 2,4, or 6. -->

By regrouping the problem variables (\\(x_i\\)) in the constraints and therefore changing the meanings of the encoding variables (\\(y_i\\)), we are able to learn additional facts about the puzzle. 
This sort of reasoning can be used by a SAT solver to more quickly prune the search space and find a solution.
Importantly, such facts cannot be learned quickly with the first encoding because the meanings of the encoding variables are less useful.


## An Experimental Evaluation

Sudoku is simple and easy to understand, making it a good example for explaining the impact of variable orderings in cardinality constraint encodings.
However, Sudoku puzzles are typically easy to solve and therefore not suitable for an experimental evaluation. 
Instead, we used more challenging problems from the 2023 Maximum Satisfiability (MaxSAT) competition. 
The annual [SAT](https://satcompetition.github.io/2023/) and [MaxSAT](https://maxsat-evaluations.github.io/2023/) competitions collect problems spanning a wide range of domains, coming from both academic and industrial sources, meant to test the limits of modern solvers.
A MaxSAT problem can be transformed into a SAT formula containing a set of clauses and one (often large) cardinality constraint.
In our experimental evaluation, we considered three options for ordering variables in the cardinality constraints:


1. Natural: use the ordering provided in the original problem encoding.
2. Random5: use five random orderings and select the one that yields the best solver runtime.
3. Proximity: use an algorithm that creates an ordering based on the proximity of variables within the problem's clauses.

After the variables were ordered, we encoded the cardinality constraints into clauses using the totalizer encoding from the Python package [PySAT](https://pysathq.github.io/), then solved the problem using the SAT solver [CaDiCaL](https://github.com/arminbiere/cadical). Each problem was solved independently with an 1800 second timeout. The results are presented in Figure 8. The plot shows the number of problems solved (y-axis) by each configuration within a given time limit (x-axis), and each tick is a new instance solved. For example, if we used the Random5 ordering and attempted to solve each problem with its own 600 second timeout, we would solve 550 of the problems. Further, with a 400 second timeout for each problem, both Proximity and Natural solve around 600 problems.

In short, the proximity approach tries to group variables that appear in constraints together.
The intuition is that if variables appear in a subset of the constraints together; by grouping them we give the solver the ability to reason locally about that subset via encoding variables.
The proximity ordering takes some time to compute, which is why it does not catch up to the natural ordering until about 400 seconds. But by the 1800 second timeout the proximity configuration solves the most formulas. So, even if it takes some additional preprocessing time to find a good ordering, it will pay off in the end.

Further, Random5 performed much worse than the other two approaches, showing that a bad ordering can seriously harm the solver's capabilities. In practice, if users are not careful with their variable orderings, they may unintentionally encode problems that are much harder to solve. 


![Plot showing the number of solved formulas within a certain time for the three variable ordering configurations. The proximity ordering solves the most, then the natural ordering, then the random ordering. The proximity ordering takes around 400 seconds to catch up to the natural ordering before overtaking it.](./cactus.png)
*Figure 8.* The number of solved formulas over time for the three variable ordering configurations.

This research was performed in collaboration with Mindy Hsu, João Filipe Boucinha de Sá, Ruben Martins, and Marijn Heule, appearing in AAAI 25 under the title "The Impact of Literal Sorting on Cardinality Constraint Encodings".


## Looking Forward

The crucial first step of solving any problem with automated reasoning is the choice of encoding.
In this post we explored the importance of a good cardinality constraint encoding and found that by simply reordering variables we can manipulate the meaning of encoding variables to improve solver performance. 
We can extend this study of cardinality constraints by considering ways to manipulate the meaning of encoding variables during solving (within the AR engine).

Additionally, there are many types of encodings for various high-level constraints that appear across problem domains in AR. 
We can begin to move away from the long-held belief that smaller encodings are always better and focus instead on the meaning of new variables introduced in the encodings.
For example, taking our strategy for improving cardinality constraint encodings and lifting it to pseudo-Boolean (cardinality with coefficients) encodings might yield similar improvements.


## References

Asín, R., Nieuwenhuis, R., Oliveras, A., and Rodríguez-Carbonell, E. 2011. Cardinality networks: a theoretical and empirical study. In Constraints An Int. J, 16(2):195–221. Springer. DOI: https://doi.org/10.1007/s10601-010-9105-0

Bailleux, O., and Boufkhad, Y. 2003. Efficient cnf encoding of boolean cardinality constraints. In Principles and Practice of Constraint Programming (CP), 108–122. Springer. DOI: https://doi.org/10.1007/978-3-540-45193-8_8

Biere, A., Fleury, M., Froleyks, N., and Heule, M. J. H. 2023. The SAT museum. In Pragmatics of SAT (POS). vol. 3545, CEUR Workshop Proceedings, pages 72-87, CEUR-WS.org. url: https://cca.informatik.uni-freiburg.de/papers/BiereFleuryFroleyksHeule-POS23.pdf

Haberlandt, A., Green, H., and Heule, M. J. H. 2023. Effective auxiliary variables via structured reencoding. In Theory and Practice of Satisfiability Testing (SAT), pp. 11:1-11:19. DOI: https://doi.org/10.4230/LIPIcs.SAT.2023.11

Klieber, W., Kwon, G. 2007. Efficient CNF encoding for selecting 1 from n objects. In Constraints in Formal Verification (CFV). p. 39. url: https://www.cs.cmu.edu/~wklieber/papers/2007_efficient-cnf-encoding-for-selecting-1.pdf

Reeves, J. E., Heule, M. J. H., and Bryant, R. E. 2024. From clauses to klauses. In Computer Aided Verification (CAV), p. 110. DOI: https://doi.org/10.1007/978-3-031-65627-9_6

<!-- 
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
(hopefully) approve your blogpost with no changes! Good luck! -->
