+++
title = "Correctness of Compilation"
date = 2026-01-04

[taxonomies]
areas = ["Programming Languages"]
tags = ["compilers", "full-abstraction", "correctness", "logical-relations", "compatibility"]

[extra]
author = {name = "Matias Scharager", url = "https://pi314mm.com/" }
committee = [
    {name = "Robert Harper", url = "https://www.cs.cmu.edu/~rwh/"},
    {name = "Jan Hoffmann", url = "https://www.cs.cmu.edu/~janh/"},
    {name = "Long Pham", url = "https://www.cs.cmu.edu/~longp/"}
]
+++

Compilation is the process of converting a human-comprehensible, mathematically rich programming language into a machine-readable, operationally explicit target language, often involving multiple sequential phases.
Compilation correctness ensures that the original program supplied by the user and the target program produced as output "do the same thing" according to our observations.

Compilation correctness has always been an important concern: even if we write wonderfully pristine code, it means nothing if bugs are injected during compilation.
This blog post will explore the complexity of verifying compilation correctness, delve into its mathematical definition, and showcase the specific approach of *type-merged correctness* we adopted in our research.
There are many hidden assumptions made during compilation that would be dangerous to overlook, but through some helpful analogies, this blog post will help you understand what properties make compilers robust and what dangers to watch out for when implementing compilation procedures.

# Difficulties in Proving Compilation Correctness

"You can't compare apples to oranges" aptly summarizes one of the main sources of complexity in compilation proofs where in this case apples and oranges correspond to programs in the source and target languages.
A source language is designed to assist programmers in solving problems that require a high level of abstraction, so it is rich with tooling and operations that are human comprehensible and mathematically inclined.
The target language is designed to be read and executed by computers, so it is filled with various operations that control internal details of computers like reading memory or loading a bus.
Since the logic the languages are working with are substantially different, the patterns of behavior within the languages are difficult to compare.
We (usually) cannot prove that the source program and compiled program have the "same" behavior; instead, we must prove they have "related" behavior according to a clearly defined notion of what "related" means.

We can use the analogy of translating between two different spoken languages, say English and Spanish, as many of the same problems occur in computer program compilation.
First, a translator would need to understand both English and Spanish to understand and translate the meaning.
Sometimes, the same exact meaning can be conveyed; there are even a lot of words in Spanish directly acquired from English.
However, sometimes the meaning gets morphed in translation, and information could get lost: a pun in English could be translated directly to Spanish, so the direct translation would make practical sense, but the humor of the pun would be lost in translation.

Let's unpack this analogy sentence by sentence and show how it can be used to describe our research method of type-merged correctness.

- A translator would need to understand both English and Spanish

Having grown up learning both English and Spanish, I often end up speaking *Spanglish*, a language that can freely blend English and Spanish language and grammar.
It is not a matter of switching back and forth between these two languages, but maintaining a mental understanding that comprehends both at the same time.

With *type-merged correctness*, we create our own version of *Spanglish* but for the source and target computer languages.
Once we have this joint language, we can compare the source and target programs through equivalence relations in the joint language since both source and target programs are expressible in the joint language.

- A lot of words in Spanish directly acquired from English

Program compilation procedures often involve multiple sequential steps, each dealing with a specific task.
Consequently, many intermediate languages have similar or possibly identical semantics, with perhaps only one small change while keeping the rest the same.
Type-merged correctness leverages this advantage, handling the easy cases efficiently so we can focus on the difficult ones, showcasing a major benefit of our approach.
However, if the source and target languages are substantially different, type-merging would still work in theory but would become much messier and less practical compared to other approaches.

- A pun in English could be translated directly to Spanish, so the direct translation would make practical sense, but the humor of the pun would be lost in translation

This analogy helps us realize that there can be several interpretations of "compilation correctness," with some guarantees being stronger than others.
While it is reasonable to consider the direct translation from English to Spanish correct because the informational content remains the same, one could also argue that it is incomplete because it fails to convey important contextual information, such as a pun in the original text.

This relates to the difference between *operational correctness* and *full abstraction correctness* in compilation.
Operational correctness states that source and target programs behave equivalently when viewed as a whole-program translation, though this equivalence is context-sensitive.
Full abstraction correctness extends this by requiring that the translation must also be context-insensitive.

Think of it this way: if we add a footnote stating "the third sentence is a pun", hence providing a context explicitly, then the direct translation from English to Spanish suffices.
However, if we try to rearrange the paragraph for clarity and the pun is no longer in the third sentence, we've created a translation error because we've lost the pun's content.
This kind of error happens more often than it should in compilation, because sometimes optimizations might be valid by the rules of the target language, but end up breaking the invisible invariants in the context that the source language intended.

A stronger translation would not only include the direct translation from English to Spanish, but would do so through a Spanish pun that conveys the same concept, allowing readers to understand the intended message regardless of contextual information.
We can build more robust compilers by incorporating the important contextual information from the source language into the compiled output.
This ensures that any optimizations acting on the compiled output do not corrupt the integrity of the program, as the contextual information is innately preserved.

Given the scale of modern programming practices where we manipulate and combine programs post-compilation, we often require full abstraction correctness in addition to operational correctness.
We need operational correctness to make sure the direct translation makes sense, but we also need full abstraction correctness to ensure this operational correctness is not conditional on hidden invariants in the contextual information.
Without this stronger guarantee, bugs could be introduced post-compilation when importing a pre-compiled library in an incompatible context, or when linking together programs from various sources and compilers that may have conflicting contextual assumptions.

Type-merged correctness is a new proof technique that can be used to verify both operational correctness and full abstraction correctness.
In the remainder of this blog post, we will dive deeper into the precise mathematical definitions of correctness and program equivalence and learn how the type-merged correctness proof is structured.
We will also witness the efficacy of this approach by applying it to continuation passing style translation and closure conversion, two well-researched compilation phases, and showing how the proofs of these can be composed together.

# Defining Correctness

We will explain the desired theorem of full abstraction correctness and operational correctness bottom-up, starting with defining the equivalence of two programs in the same language.

## Program Equivalence

There are two levels of granularity in program equivalence that we wish to consider depending on if we are comparing over expressions or whole programs.
An expression is any well-typed program that may rely on variables defined in an external context.
A whole program is an expression with two additional properties: it is not depending on any open-scoped variables (whole programs are closed), and upon termination it returns a value of the chosen "answer type."
We fix our answer type to be booleans, hence whole programs are decision algorithms that either accept or reject.

*Kleene equivalence* is a definition of whole program equivalence.
It is broken into three cases: either both programs infinitely loop, both programs terminate and accept, or both programs terminate and reject.
We know for certain that for every whole program, one of these three cases must occur.

Now how can we bootstrap Kleene equivalence to compare equality between arbitrary expressions instead of just whole programs?
There are several ways to do this, and the definition we opt for is *contextual equivalence*.

First, a *program context* is defined as a whole program with a single hole that should be filled.
Think of this as a partially written program with a fill-in-the-blank where we will paste our implementation.
Two expressions are contextually equivalent by definition if when we paste them into *any* arbitrarily chosen program context, the two resulting whole programs are Kleene equivalent.

One can think of program contexts as test cases for verifying the equivalence of two expressions.
The fact that contextual equivalence quantifies over *any* arbitrarily chosen program context indicates that the expressions are equivalent for *any* possible test cases, even really obscure test cases.
It is not always enough to test a finite number of test cases to reach contextual equivalence: if a function works for inputs 0 to n, how do we know it still works for n+1?
This makes contextual equivalence difficult to work with because we need a stronger mathematical understanding of the behavior of the underlying programs to be able to prove it.

Thankfully, we can define this helpful tool known as a logical relation for these proofs of contextual equivalence.
A *logical relation* is defined inductively on the type structure of the programs it is comparing, so we can leverage type information about the program to prove *logical equivalence*.
We define a logical relation in such a way that gives us the tools to analyze the programs we want to work with but also ensures that logical equivalence and contextual equivalence relate the same things.

## Notation

For consistency, we will refer to source expressions as \\(s\\) and target programs as \\(t\\).
If we write \\(s1\\) and \\(t1\\) for consistent numbers, we are indicating that the source expression \\(s1\\) gets compiled into the target program output \\(t1\\).

For types, we will use \\(\tau\\) to refer to source types and \\(\overline{\tau}\\) to refer to their compiled target type.
In the base type, \\(\textbf{bool}\\), we have that \\(\overline{\textbf{bool}} = \textbf{bool}\\), so we omit the overscore.

Source programs, target programs, and contextual equivalence are all represesented in the common domain the joint language created through the type-merging approach.
When we do not need to distingush between source and target languages, we use \\(e\\) and \\(\varphi\\) to describe an arbitrary program and type in the joint language.

Contextual equivalence should be fully expressed with a typing context and resulting type as \\(\Gamma \vdash e_1 \equiv e_2 : \varphi\\).
For simplicity in presentation, we will often erase these and express contextual equivalence as \\(e_1 \equiv e_2\\), but rest assured that the typing context is explictly handled in the proofs.


## Full Abstraction Correctness

Formally, full abstraction correctness is defined as: if two source programs \\(s1\\) and \\(s2\\) compile to target programs \\(t1\\) and \\(t2\\) respectively, then \\(s1 \equiv s2\\) if and only if \\(t1 \equiv t2\\).

Contextual equivalence between programs inherently defines a type interface between the programs and an abstraction guarantee that the programs provide the same results under that interface.
This interface is explicitly granted through the logical equivalence which we have proven corresponds to contextual equivalence.
A compiler that is fully abstract preserves these abstractions through compilation, meaning that the same interface that exists between \\(s1\\) and \\(s2\\) still exists between \\(t1\\) and \\(t2\\) without imposing additional restrictions as to how \\(t1\\) and \\(t2\\) should be used to preserve this interface.

A reasonable example of breaking abstraction would be when a source program requires a specific memory location \\(m\\) to be "nonzero" and only allows you to reference this memory location through functions that preserve \\(m\neq 0\\).
Naively compiling this could accidentally expose \\(m\\) to other parts of the program. Abstraction is preserved only if those other parts of the program abide by the rule of \\(m\neq 0\\).
Since this restriction is not enforced by the types or the language itself, it creates opportunities for a wide variety of bugs resulting from failure to preserve this invariant.

From a practical perspective, full abstraction correctness gives us the ability to "hot-swap" code at any stage of compilation, since contextual equivalence is preserved through compilation and is both compatible and transitive.
This capability is the driving force of many modern software practices.
If we want to change a single line of code in the source language but have already spent significant time compiling the old program, we can just recompile that single line on its own and hot-swap the old version post-compilation while still resulting in a correct compilation.
This notion of correctness also enables optimizations at any stage of compilation: we can perform a partial hot-swap of code at any compilation stage and still maintain the overall correctness proof.
The structure of this definition also allows for stacking arbitrarily many compilation phases together; we just need to show that contextual equivalence is preserved at each stage.

We need both full abstraction correctness and operational correctness to truly be able to say the compilation strategy makes sense, and neither form of correctness directly implies the other.
However, it is possible to prove a single stronger theorem and use it to derive corollaries of both full abstraction correctness and operational correctness directly.
In the next section, we will discover that big theorem through the process of trying to prove full abstraction correctness.

## Proving Correctness

Let's take two arbitrary source programs \\(s1\\) and \\(s2\\) which compile to target programs \\(t1\\) and \\(t2\\) respectively.
To prove the forward direction of full abstraction correctness, we assume \\(s1 \equiv s2\\), and we aim to show that \\(t1\equiv t2\\).

If the source and target languages were the same and the types of programs didn't change during compilation (not an interesting compiler), then just knowing that the source and target programs are contextually equivalent is enough to prove full abstraction correctness by symmetry and transitivity of contextual-equivalence.

$$t1 \equiv s1 \equiv s2 \equiv t2$$

However, in most cases, the source and target programs are not directly contextually equivalent but are contextually equivalent over a chosen interface.
This interface is defined through functions \\(\mathbf{over}\\) and \\(\mathbf{back}\\) that relate the logic of the source and target languages.
The function \\(\mathbf{over}\\) wraps an interface around a source program so it can be understood in the target language, and the \\(\mathbf{back}\\) wraps an interface around the target program so it can be understood in the source language.
We define \\(\mathbf{over}\\) and \\(\mathbf{back}\\) inductively based on the type of the input, where we set \\(\mathbf{over}\\) and \\(\mathbf{back}\\) at the base answer type of booleans to be the identity function.
We prove that these two interfaces are inverses of each other within the joint language, meaning for any joint language expressions \\(e1\\) and \\(e2\\) of the appropriate types, \\(e1\equiv \mathbf{back}(\mathbf{over}(e1))\\) and \\(e2 \equiv \mathbf{over}(\mathbf{back}(e2)) \\).

To get full abstraction correctness, it is enough to prove that for any pair of source and its compiled output \\(s \\) and \\(t\\), we have \\(s \equiv \mathbf{back}(t)\\) or equivalently that \\(\mathbf{over}(s) \equiv t\\).

$$t1 \equiv \mathbf{over}(s1) \equiv \mathbf{over}(s2) \equiv t2$$

It remains to show that \\(\mathbf{over}(s) \equiv t\\) for any source and its compiled output.
Notably, operational correctness is the special case of this theorem when \\(s\\) is a whole program and falls out as a corollary.
In that case, \\(\mathbf{over}\\) is the identity function so we have \\(s \equiv \mathbf{over}(s) \equiv t\\), and contextual equivalence of whole programs implies Kleene equivalence of those same programs under the empty context, so \\(s\\) is Kleene equivalent to \\(t\\).

To prove this big theorem of \\(\mathbf{over}(s) \equiv t\\), we carefully induct through each possible case of compilation pairs \\(s\\) and \\(t\\).
We rely on type information, expanding out the definitions of \\(\mathbf{over}\\) and \\(\mathbf{back}\\), and using the logical relation at these types to prove contextual equivalence.
This is a lengthy proof, but straightforward once you have the proper definitions of \\(\mathbf{over}\\), \\(\mathbf{back}\\), and the logical relation, all of which were meticulously defined precisely to make this proof work out and grant us the intended contextual equivalence result.

## Defining Over and Back

There can be multiple ways of defining \\(\mathbf{over}\\) and \\(\mathbf{back}\\).
The necessary restrictions we have are that they are inverses of each other, they are contextually equivalent to the identity function at the base type, and the big theorem of \\(\mathbf{over}(s) \equiv t\\) holds true.

The novel contribution of the type-merging correctness approach is that we can then define \\(\mathbf{over}\\) and \\(\mathbf{back}\\) as functions within the joint language itself, and use contextual-equivalence within the joint language to show that \\(\mathbf{over}\\) and \\(\mathbf{back}\\) are mutual inverses.
Other related approaches [[1]](#references) embed \\(\mathbf{over}\\) and \\(\mathbf{back}\\) as syntactic constructs of the joint language, but add complications in the safety proof of the joint language.

We opt for the simplest definitions we can find, or the simplest type coersions \\(\mathbf{over} : \tau \to \overline{\tau}\\) and \\(\mathbf{back} : \overline{\tau}\to\tau\\) defined inductively on the type \\(\tau\\) where the compilation strategy converts source language type \\(\tau\\) to the target language type \\(\overline{\tau}\\), and we prove that these properties hold for the chosen functions.

The conversions are pretty easy to define in the inductive cases where the compilation strategy does not do much other than inductively carry out the translation.
For instance, consider the case of compiling pairs by just compiling each side separately without change, so \\(\tau_1 \times \tau_2\\) compiles to \\(\overline {\tau_1} \times \overline{\tau_2}\\).
The conversions at these types are defined similarly to an eta-expansion, in other words, they just carry the induction hypothesis along smoothly without doing anything complicated.

Type-merging correctness works really well when the source and target languages have similar semantics, and in practice, especially for higher-order compilation, it is often the case that the target language is a simplified subset of the source language, meaning we can just utilize the source language itself as the joint language.
This way, we separate the proof of the type-safety of the joint language from the overall compilation correctness proof, and in fact, we find we can reuse the same joint language for multiple layered phases of compilation, each with its definition of \\(\mathbf{over}\\) and \\(\mathbf{back}\\).

A related work that showcases this is Crary's work on Fully Abstract Module Compilation. [[2]](#references)
This employs a phase-separation algorithm for splitting modules into static and dynamic portions without reference to the module language.
This means we can go from a rich expressive language with modules as the source language, compile away the modules through this phase-separation technique, and arrive at a simpler target language without modules.
In this case, the joint language is rather close to the source language itself.

## Intensional vs Extensional Compilation

You might be wondering, is \\(\mathbf{over}\\) the same as the compilation itself?
If it were, then this result is rather obvious because we would be comparing the compilation to the compilation.
To illustrate the difference, let's look at an example program and a silly compilation phase that computes every function argument twice.
Assume that t1 and t2 are the fully compiled versions of s1 and s2 respectively.

```ocaml
(* source *)
let f x : bool = s1;;
f (s2)

(* compiled *)
let g x y : bool = t1;;
g (t2) (t2)
```

Here, we see that the source program f only recieves one argument s2, but the resulting compiled function g recieves the same argument t2 two times.
There are not many practical merits to this transformation, but it illustrates the point that the compiler is syntax aware: it doubles the input arguments in every function definition and duplicates the function argument in every function call.
This transformation affects the function type only, and importantly, the bool type which is our answer type does not change.

Meanwhile, one of the restrictions of the \\(\mathbf{over}\\) and \\(\mathbf{back}\\) functions is that their definitions at the base type is contextually equivalent to the identity function, and the whole program we are compiling happens to be of the base type, bool.
Even though the compiler is doing a lot of stuff, the \\(\mathbf{over}\\) function we use in our proof does not do anything at all, and just returns the original input as is.

The distinction lies in that the compiler can observe how the expression is defined and can chop up the syntax however it likes to produce a compiled result, but the \\(\mathbf{over}\\) and \\(\mathbf{back}\\) functions only know the overall type of the expression.
In this sense, the compiler is a conversion of the *intensional* properties of the program where the way the program is implemented does matter, whereas the \\(\mathbf{over}\\) function is a relation of the *extensional* behavior of the program.
The \\(\mathbf{over}\\) function is an interface wrapping up the program in a way that abstracts away the particular implementation, leaving us only able to condition the final result value we get from executing the program.
By comparing the compiler to the \\(\mathbf{over}\\) function, we are stating that the *intensional* changes the compiler makes adhere to the *extensional* properties of the original program, which is a really strong statement of correctness.

# Proof of Concept

To demonstrate the efficacy of type-merging correctness, we proved the correctness of two separate compilation phases and then joined these two proofs together.
This takes us from an ML-like source language with control-flow effects and anonymous functions to a target language that has those two features compiled away.

## Continuation Passing Style Phase

The continuation passing style (CPS) translation [[3]](#references) is commonly used to cleanly express the control-flow of programs.
We convert a term \\(s\\) into a pair \\((k,t)\\) where \\(t\\) is a computation, and \\(k\\) is a continuation for which the computation returns a value once it is finished running.
Normally, there is a one-to-one correspondence: \\(t\\) only produces one value which gets sent to the continuation \\(k\\) at one location, but this translation phase becomes most interesting when we add control-flow effects into our language which breaks this one-to-one correspondence.
The CPS translation can tame all these control-flow effects, leaving us in a simpler language without explicit control-flow operations.

Our source language contains the explicit control-flow operations of \\(\mathbf{letcc}\\) and \\(\mathbf{throw}\\).
The construct \\(\mathbf{letcc}\\) allows us to record the current state of the computer and save it as a continuation while \\(\mathbf{throw}\\) lets us jump to some previous state of the computer by calling the respective continuation.
You can pretend it is similar to an assembly jump operation, so you can imagine how it could be used to express conditional branching and short-circuiting of computations.

Interestingly, \\(\mathbf{over}\\) and \\(\mathbf{back}\\) for the CPS translation must use these control-flow mechanisms within its definition.
Thankfully, we can prove that these particular control-flow effects within the \\(\mathbf{over}\\) and \\(\mathbf{back}\\) are benign so we can maintain the properties we want with some extra effort.

## Closure Conversion Phase

A closure is an inline function that can utilize the initialized variables in the context within its definition.
Closure conversion (CC) translation [[4]](#references) takes these closures and turns them into global function definitions that can be moved into the top level instead of inlined.
It achieves this by packaging the variables in the context that the closure depends on into a large tuple and passing them as input into the global function to maintain the dependency.

Central to the proof of this phase is a *parametricity* relation between the original closure function and the resulting global function.
Parametricity allows us to show that two programs are contextually equivalent even if they are of different types, as long as we can state an interface where the types are related.
Function application through compilation becomes a parametric packing operation before calling the function, granting us the interface we need in the proof of full abstraction correctness.

## Joining it All Together

Our final theorem for full abstraction correctness states that if we have start with source programs \\(s_1\\) and \\(s_2\\), and put them both through both phases of compilation to get \\(t_1\\) and \\(t_2\\) respectively with continuation variable \\(k\\), then we know that
$$\Gamma \vdash s_1 \equiv s_2 : \tau\ \ \text{if and only if}\ \ \overline{\Gamma}, k : \overline{\tau}\to0\vdash t_1\equiv t_2 : 0.$$
This essentially says that the equivalent programs \\(s_1\\) and \\(s_2\\) compile into equivalent programs \\(t_1\\) and \\(t_2\\), even with both phases of compilation put together.
We are extra pedantic with the notation for this final lemma.
Note that the CPS phase adds a new variable \\(k\\) representing the continuation to the context of open variables \\(\Gamma\\).
The type \\(0\\) represents the empty type as the compiled term calls the continuation instead of returning a value.

We successfully demonstrate that this correctness approach works for these two phases of compilation by rigorously proving this theorem.
With this, we have completed our proof of full abstraction compilation correctness for two compilation passes layered together utilizing a single joint language definition.
In future work, we hope to add more layers of compilation to our proof and tackle some difficult compilation phases such as memory allocation and garbage collection.

# References
<style>
dl {
  display: grid;
  overflow: hidden;
  grid-template-columns: max-content minmax(0,1fr);
}

dt {
  grid-column-start: 1;
}

dd {
  grid-column-start: 2;
}
</style>
<dl>
  <dt>[1]</dt><dd>Ahmed, Amal, and Matthias Blume. "An equivalence-preserving CPS translation via multi-language semantics." <i>Proceedings of the 16th ACM SIGPLAN international conference on Functional programming</i>. 2011.</dd>
  <dt>[2]</dt><dd>Crary, Karl. "Fully abstract module compilation." <i>Proceedings of the ACM on Programming Languages</i> 3.POPL (2019): 1-29.</dd>
  <dt>[3]</dt><dd>Harper, Robert, and Mark Lillibridge. "Explicit polymorphism and CPS conversion." <i>Proceedings of the 20th ACM SIGPLAN-SIGACT symposium on principles of programming languages</i>. 1993.</dd>
  <dt>[4]</dt><dd>Minamide, Yasuhiko, Greg Morrisett, and Robert Harper. "Typed closure conversion." <i>Proceedings of the 23rd ACM SIGPLAN-SIGACT symposium on principles of programming languages</i>. 1996.</dd>
</dl>