+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "Amortized Analysis as a Cost-Aware Abstraction Function"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2025-05-14

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Programming Languages", "Theory"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
# Consider these similar to keywords specified for a research paper.
tags = [
    "amortized",
    "cost",
    "data structures",
    "homomorphism",
    "physicists method",
    "resource analysis",
    "program verification"
]

[extra]
author = {name = "Harrison Grodin", url = "https://www.harrisongrodin.com/" }
# The committee specification is a list of objects similar to the author.
committee = [
    {name = "Guy Blelloch", url = "https://www.cs.cmu.edu/~guyb/"},
    {name = "Frank Pfenning", url = "https://www.cs.cmu.edu/~fp/"},
    {name = "Long Pham", url = "https://www.cs.cmu.edu/~longp/"}
]
+++

Data structures contain two important aspects that computer scientists seek to verify: behavior and cost.
The behavior of data structures has long been studied using abstraction functions, which translate concrete data structure representations into a semantic representation.
On the other hand, the cost associated with data structures has been analyzed using the method of amortization, a technique in which cost is studied in aggregate: rather than considering the maximum cost of a single operation, one bounds the total cost encountered throughout a sequence of operations.
In this post, I will demonstrate how to unify these two techniques, packaging the data associated with an amortized analysis as an abstraction function that incorporates cost.
This reframing is more amenable to formal verification, consolidates prior variations of amortized analysis, and generalizes amortization to novel settings.
This work was published at [MFPS 2024](https://entics.episciences.org/14797).

First, I will introduce an example data structure: the batched queue.
After sketching a proof of the behavioral correctness of this data structure using an abstraction function, I will review how to use the method of amortization to analyze the cost associated to this data structure.
Finally, I will describe how to embed the essence of amortized analysis into an abstraction function, thereby creating a unified framework for reasoning about both the behavior and the cost of data structures.


# Motivating example: batched queues {#batched-queue}

To keep our discussion concrete, let's use a concrete choice of amortized data structure as a running example in this post: the *batched queue*.
Setting the scene, consider the [queue](https://en.wikipedia.org/wiki/Queue_(abstract_data_type)) abstract data type, which describes finite lists of data that can be "enqueued" to and "dequeued" from in a first-in, first-out manner.
This description of operations can be given the following types, written in [OCaml syntax](https://ocaml.org/manual/latest/index.html):
```ocaml
module type QUEUE = sig
  type t

  val empty : unit -> t
  val enqueue : int -> t -> t
  val dequeue : t -> int * t
end
```
To implement `QUEUE`, we must choose a representation type `t` and implement operations on this type `t` to create an empty queue, enqueue an element, and dequeue an element.
The simplest implementation chooses representation type `t = int list`:
```ocaml
module ListQueue : QUEUE with type t = int list = struct
  type t = int list

  let empty () = []

  let enqueue x l = l @ [ x ]

  let dequeue = function
    | [] -> 0, []
    | x :: l -> x, l
  ;;
end
```
The empty queue is represented as the empty list `[]`; enqueueing `x` uses the `( @ )` function to append the singleton list `[ x ]`; and dequeueing pattern matches on the given list (either empty `[]` or nonempty `x :: l`), returning `0` as a default element when the queue is empty.
We can run a simple test case to check the behavior of this code as follows:
```ocaml
let demo =
  LQ.empty ()      (* []     *)
  |> LQ.enqueue 1  (* [1]    *)
  |> LQ.enqueue 2  (* [1; 2] *)
  |> LQ.dequeue    (* 1, [2] *)
;;
```
Here, letting `LQ` be an alias for `ListQueue`, we use the pipe operator `x |> f = f x` to create and interact with a queue.
We start with the empty queue `LQ.empty ()`, enqueue the numbers `1` and `2`, and then dequeue from the queue.
Indeed, the dequeued result is `1` with remaining queue `[2]`, as expected.

While this implementation clearly conveys the intended behavior of a queue, it lacks in efficiency: the implementation of the enqueue operation takes linear time in the length of the list representing the queue.
Therefore, it is best to treat this implementation as a specification only, describing how a more efficient queue ought to be implemented.

For an alternative implementation, sometimes referred to as a [batched queue](https://en.wikipedia.org/wiki/Queue_(abstract_data_type)#Amortized_queue), we can choose the representation type to be pairs of lists, `t = int list * int list`.
Every queue state is now a pair of lists `inbox, outbox`, where the inbox list is in reverse order.
A queue can now have more than one representation; for example, the queue containing elements `[1; 2]` can be represented as
- `[], [1; 2]`,
- `[2], [1]`, or
- `[2; 1], []`.

We implement the operations as follows:
```ocaml
module BatchedQueue : QUEUE with type t = int list * int list = struct
  type t = int list * int list

  let empty () = [], []

  let enqueue x (inbox, outbox) = x :: inbox, outbox

  let dequeue = function
    | inbox, x :: outbox -> x, (inbox, outbox)
    | inbox, [] ->
      (match List.rev inbox with
       | x :: outbox -> x, ([], outbox)
       | [] -> 0, ([], []))
  ;;
end
```
The empty queue starts with both the inbox and outbox being empty, and the enqueue operation simply adds the new element `x` to the inbox.
The implementation of the dequeue operation is more complex:
1. In case the outbox is nonempty (*i.e.*, of the form `x :: outbox`), we dequeue this element `x`, leaving the inbox alone and updating the outbox to the remaining outbox from this list.
2. If the outbox is empty, we use `List.rev` to reverse the inbox and treat it as the new outbox. Then, we attempt to take the first element from this new outbox. If the inbox was also empty, we return default element `0` and leave both the inbox and the outbox empty.

Compared to `ListQueue`, it is less obvious that `BatchedQueue` correctly implements the queue abstraction.
We can run the same test case before as a simple check, swapping `ListQueue` for `BatchedQueue`, shortened as `BQ`:
```ocaml
let demo =
  BQ.empty ()      (* [], []       *)
  |> BQ.enqueue 1  (* [1], []      *)
  |> BQ.enqueue 2  (* [2; 1], []   *)
  |> BQ.dequeue    (* 1, ([], [2]) *)
;;
```
Here, the result is `1, ([], [2])`, dequeueing element `1` as before and giving a batched queue representing `[2]`, here `([], [2])`.
How can we prove that this will always be the case, though?
Let's discuss the proof technique that shows how we can verify the correctness of `BatchedQueue` relative to `ListQueue`.
Then, we can analyze the cost of `BatchedQueue`.


# Abstraction functions: behavioral verification of data structures {#abstraction-function}

To verify that `BatchedQueue` is correct relative to the specification `ListQueue`, we use an *abstraction function* that converts a batched queue state to a single list representing the same state.
This venerable idea goes back to Tony Hoare:

> The first requirement for the proof [of correctness] is to define the relationship between the abstract space in which the abstract program is written, and the space of the concrete representation.
> This can be accomplished by giving a function [\\( \alpha \\)] which maps the concrete variables into the abstract object which they represent.
> Note that in this and in many other cases [\\( \alpha \\)] will be a many-one function.
> Thus there is no unique concrete value representing any abstract one.
> <div style="text-align: right"> &ndash;Hoare, 1972, <a href="https://dl.acm.org/doi/abs/10.5555/63445.C1104363">Proof of Correctness of Data Representations</a> </div>

For our example, we can implement the abstraction function as follows, rendering \\( \alpha \\) as `alpha` in code:
```ocaml
let alpha : BatchedQueue.t -> ListQueue.t =
  fun (inbox, outbox) -> outbox @ List.rev inbox
;;
```
We turn `inbox, outbox` into a single list by appending the reversed `inbox` list to the `outbox` list.
For example, the pair `[4; 3], [1; 2]` will be mapped by the `alpha` function to the list `[1; 2; 3; 4]`.

Now, to verify the operations are correct, we must show that the `BatchedQueue` operations cohere with the simpler `ListQueue` operations, mediated by this function, `alpha`.
In mathematical parlance, this is called showing that `alpha` is a *`QUEUE`-homomorphism*.
Let us abbreviate `BatchedQueue` as `BQ` and `ListQueue` as `LQ`; concretely, this means checking the following conditions, one per operation in the `QUEUE` interface:
1. \\( \alpha(\texttt{BQ.empty ()}) = \texttt{LQ.empty ()} \\),
2. \\( \alpha(\texttt{BQ.enqueue}\ x~q) = \texttt{LQ.enqueue}\ x~(\alpha~q) \\) for all \\( q : \texttt{BQ.t} \\), and
3. \\( \alpha^\prime(\texttt{BQ.dequeue}\ q) = \texttt{LQ.dequeue}\ (\alpha~q) \\) for all \\( q : \texttt{BQ.t} \\), where \\( \alpha^\prime(x, q^\prime) = (x, \alpha(q^\prime)) \\) applies the abstraction function to the second component of a pair of type \\( \texttt{int * BQ.t} \\).

These conditions can be visualized using the following diagrams.
Each square represents one of the above equations, stating that the two paths (right/down ↴ and down/right ↳) are equivalent.
In mathematics, when both paths are equivalent, we say that the square *commutes*.

<style>
.column {
  float: left;
  padding: 12px;
}

.small {
  width: 25%;
}

.large {
  width: 35%;
}

/* Clear floats after the columns */
.row:after {
  content: "";
  display: table;
  clear: both;
}
</style>
<div class="row">
  <div class="column small">
<!-- https://q.uiver.app/#q=WzAsNCxbMSwwLCJcXHRleHR0dHtCUS50fSJdLFswLDAsIlxcdGV4dHR0e3VuaXR9Il0sWzEsMSwiXFx0ZXh0dHR7TFEudH0iXSxbMCwxLCJcXHRleHR0dHt1bml0fSJdLFswLDIsIlxcYWxwaGEiXSxbMSwwLCJcXHRleHR0dHtCUS5lbXB0eX0iXSxbMywyLCJcXHRleHR0dHtMUS5lbXB0eX0iLDJdLFsxLDMsIiIsMix7InN0eWxlIjp7ImhlYWQiOnsibmFtZSI6Im5vbmUifX19XV0= -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsNCxbMSwwLCJcXHRleHR0dHtCUS50fSJdLFswLDAsIlxcdGV4dHR0e3VuaXR9Il0sWzEsMSwiXFx0ZXh0dHR7TFEudH0iXSxbMCwxLCJcXHRleHR0dHt1bml0fSJdLFswLDIsIlxcYWxwaGEiXSxbMSwwLCJcXHRleHR0dHtCUS5lbXB0eX0iXSxbMywyLCJcXHRleHR0dHtMUS5lbXB0eX0iLDJdLFsxLDMsIiIsMix7InN0eWxlIjp7ImhlYWQiOnsibmFtZSI6Im5vbmUifX19XV0=&embed" width="250" height="250" style="border-radius: 8px; border: none;"></iframe>
  </div>
  <div class="column small">
<!-- https://q.uiver.app/#q=WzAsNCxbMSwwLCJcXHRleHR0dHtCUS50fSJdLFswLDAsIlxcdGV4dHR0e0JRLnR9Il0sWzEsMSwiXFx0ZXh0dHR7TFEudH0iXSxbMCwxLCJcXHRleHR0dHtMUS50fSJdLFswLDIsIlxcYWxwaGEiXSxbMSwwLCJcXHRleHR0dHtCUS5lbnF1ZXVlIHh9Il0sWzMsMiwiXFx0ZXh0dHR7TFEuZW5xdWV1ZSB4fSIsMl0sWzEsMywiXFxhbHBoYSJdXQ== -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsNCxbMSwwLCJcXHRleHR0dHtCUS50fSJdLFswLDAsIlxcdGV4dHR0e0JRLnR9Il0sWzEsMSwiXFx0ZXh0dHR7TFEudH0iXSxbMCwxLCJcXHRleHR0dHtMUS50fSJdLFswLDIsIlxcYWxwaGEiXSxbMSwwLCJcXHRleHR0dHtCUS5lbnF1ZXVlIHh9Il0sWzMsMiwiXFx0ZXh0dHR7TFEuZW5xdWV1ZSB4fSIsMl0sWzEsMywiXFxhbHBoYSJdXQ==&embed" width="250" height="250" style="border-radius: 8px; border: none;"></iframe>
  </div>
  <div class="column large">
<!-- https://q.uiver.app/#q=WzAsNCxbMSwwLCJcXHRleHR0dHtpbnR9IFxcYXN0IFxcdGV4dHR0e0JRLnR9Il0sWzAsMCwiXFx0ZXh0dHR7QlEudH0iXSxbMSwxLCJcXHRleHR0dHtpbnR9IFxcYXN0IFxcdGV4dHR0e0xRLnR9Il0sWzAsMSwiXFx0ZXh0dHR7TFEudH0iXSxbMCwyLCJcXGFscGhhJyJdLFsxLDAsIlxcdGV4dHR0e0JRLmRlcXVldWV9Il0sWzMsMiwiXFx0ZXh0dHR7TFEuZGVxdWV1ZX0iLDJdLFsxLDMsIlxcYWxwaGEiXV0= -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsNCxbMSwwLCJcXHRleHR0dHtpbnR9IFxcYXN0IFxcdGV4dHR0e0JRLnR9Il0sWzAsMCwiXFx0ZXh0dHR7QlEudH0iXSxbMSwxLCJcXHRleHR0dHtpbnR9IFxcYXN0IFxcdGV4dHR0e0xRLnR9Il0sWzAsMSwiXFx0ZXh0dHR7TFEudH0iXSxbMCwyLCJcXGFscGhhJyJdLFsxLDAsIlxcdGV4dHR0e0JRLmRlcXVldWV9Il0sWzMsMiwiXFx0ZXh0dHR7TFEuZGVxdWV1ZX0iLDJdLFsxLDMsIlxcYWxwaGEiXV0=&embed" width="300" height="250" style="border-radius: 8px; border: none;"></iframe>
  </div>
</div>

In fact, these conditions do hold, which we sketch the proofs of as follows.
First, `alpha` preserves `empty`:
```ocaml
alpha (BatchedQueue.empty ())
= alpha ([], [])
= []
= ListQueue.empty ()
```
Next, `alpha` preserves `enqueue`:
```ocaml
alpha (BatchedQueue.enqueue x (inbox, outbox))
= alpha (x :: inbox, outbox)
= outbox @ List.rev (x :: inbox)
= outbox @ List.rev inbox @ [ x ]  (* lemma *)
= alpha (inbox, outbox) @ [ x ]
= ListQueue.enqueue x (alpha (inbox, outbox))
```
All steps follow by unfolding definitions, aside from the line indicated, which uses a lemma about the list reversal function `List.rev` and the append function `( @ )`.
We omit the slightly more involved proof that `alpha` preserves `dequeue`, which goes by cases following the structure of the `BatchedQueue.dequeue` code.

Observe that the conditions can be combined to relate the results of sequences of operations, where each successive operation transforms the queue created by the previous one.
In our sample trace, we may apply `alpha` between any two operations, and the result will be unaffected; for example, we may place `alpha` after the first enqueue as follows, using `BatchedQueue` before this point and `ListQueue` after this point.
```ocaml,hl_lines=4-6
let demo =
  BQ.empty ()            (* [], []  *)
  |> BQ.enqueue 1        (* [1], [] *)
  (* ⬆️ batched queue *)
  |> alpha               (* [1]     *)
  (* ⬇️ list queue *)
  |> LQ.enqueue 2        (* [1; 2]  *)
  |> LQ.dequeue          (* 1, [2]  *)
;;
```
Above the divider, the trace matches that for `BatchedQueue`, and below the divider, the trace matches that for `ListQueue`.
The divider may be moved to any point in the code without changing the final result.

Diagrammatically, such equivalences are visualized as horizontal juxtaposition of commutative squares (omitting `BQ` and `LQ` on operation names for space):
<!-- https://q.uiver.app/#q=WzAsMTAsWzQsMCwiXFx0ZXh0dHR7aW50fSBcXGFzdCBcXHRleHR0dHtCUS50fSJdLFsyLDAsIlxcdGV4dHR0e0JRLnR9Il0sWzQsMSwiXFx0ZXh0dHR7aW50fSBcXGFzdCBcXHRleHR0dHtMUS50fSJdLFsyLDEsIlxcdGV4dHR0e0xRLnR9Il0sWzAsMCwiXFx0ZXh0dHR7dW5pdH0iXSxbMCwxLCJcXHRleHR0dHt1bml0fSJdLFsxLDAsIlxcdGV4dHR0e0JRLnR9Il0sWzEsMSwiXFx0ZXh0dHR7TFEudH0iXSxbMywwLCJcXHRleHR0dHtCUS50fSJdLFszLDEsIlxcdGV4dHR0e0xRLnR9Il0sWzAsMiwiXFxhbHBoYSciXSxbMSwzLCJcXGFscGhhIiwwLHsiY29sb3VyIjpbMCw2MCw2MF19LFswLDYwLDYwLDFdXSxbNCw1LCIiLDAseyJzdHlsZSI6eyJoZWFkIjp7Im5hbWUiOiJub25lIn19fV0sWzQsNiwiXFx0ZXh0dHR7ZW1wdHl9IiwwLHsiY29sb3VyIjpbMCw2MCw2MF19LFswLDYwLDYwLDFdXSxbNSw3LCJcXHRleHR0dHtlbXB0eX0iLDJdLFs3LDMsIlxcdGV4dHR0e2VucXVldWV9fjEiLDJdLFs2LDEsIlxcdGV4dHR0e2VucXVldWV9fjEiLDAseyJjb2xvdXIiOlswLDYwLDYwXX0sWzAsNjAsNjAsMV1dLFs2LDcsIlxcYWxwaGEiXSxbOCwwLCJcXHRleHR0dHtkZXF1ZXVlfSJdLFs5LDIsIlxcdGV4dHR0e2RlcXVldWV9IiwyLHsiY29sb3VyIjpbMCw2MCw2MF19LFswLDYwLDYwLDFdXSxbMSw4LCJcXHRleHR0dHtlbnF1ZXVlfX4yIl0sWzMsOSwiXFx0ZXh0dHR7ZW5xdWV1ZX1+MiIsMix7ImNvbG91ciI6WzAsNjAsNjBdfSxbMCw2MCw2MCwxXV0sWzgsOSwiXFxhbHBoYSJdXQ== -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsMTAsWzQsMCwiXFx0ZXh0dHR7aW50fSBcXGFzdCBcXHRleHR0dHtCUS50fSJdLFsyLDAsIlxcdGV4dHR0e0JRLnR9Il0sWzQsMSwiXFx0ZXh0dHR7aW50fSBcXGFzdCBcXHRleHR0dHtMUS50fSJdLFsyLDEsIlxcdGV4dHR0e0xRLnR9Il0sWzAsMCwiXFx0ZXh0dHR7dW5pdH0iXSxbMCwxLCJcXHRleHR0dHt1bml0fSJdLFsxLDAsIlxcdGV4dHR0e0JRLnR9Il0sWzEsMSwiXFx0ZXh0dHR7TFEudH0iXSxbMywwLCJcXHRleHR0dHtCUS50fSJdLFszLDEsIlxcdGV4dHR0e0xRLnR9Il0sWzAsMiwiXFxhbHBoYSciXSxbMSwzLCJcXGFscGhhIiwwLHsiY29sb3VyIjpbMCw2MCw2MF19LFswLDYwLDYwLDFdXSxbNCw1LCIiLDAseyJzdHlsZSI6eyJoZWFkIjp7Im5hbWUiOiJub25lIn19fV0sWzQsNiwiXFx0ZXh0dHR7ZW1wdHl9IiwwLHsiY29sb3VyIjpbMCw2MCw2MF19LFswLDYwLDYwLDFdXSxbNSw3LCJcXHRleHR0dHtlbXB0eX0iLDJdLFs3LDMsIlxcdGV4dHR0e2VucXVldWV9fjEiLDJdLFs2LDEsIlxcdGV4dHR0e2VucXVldWV9fjEiLDAseyJjb2xvdXIiOlswLDYwLDYwXX0sWzAsNjAsNjAsMV1dLFs2LDcsIlxcYWxwaGEiXSxbOCwwLCJcXHRleHR0dHtkZXF1ZXVlfSJdLFs5LDIsIlxcdGV4dHR0e2RlcXVldWV9IiwyLHsiY29sb3VyIjpbMCw2MCw2MF19LFswLDYwLDYwLDFdXSxbMSw4LCJcXHRleHR0dHtlbnF1ZXVlfX4yIl0sWzMsOSwiXFx0ZXh0dHR7ZW5xdWV1ZX1+MiIsMix7ImNvbG91ciI6WzAsNjAsNjBdfSxbMCw2MCw2MCwxXV0sWzgsOSwiXFxhbHBoYSJdXQ==&embed" width="750" height="250" style="border-radius: 8px; border: none;"></iframe>

The path taken in the `demo` code sample is highlighted in red.
Tracing the data, we see all the possible equivalent paths for `demo` depending on where we choose to place the `alpha` translation, which moves from the top edge to the bottom edge.
<!-- https://q.uiver.app/#q=WzAsMTAsWzQsMCwiXFx0ZXh0dHR7MSwoW10sWzJdKX0iXSxbMiwwLCJcXHRleHR0dHtbMV0sW119Il0sWzQsMSwiXFx0ZXh0dHR7MSxbMl19Il0sWzIsMSwiXFx0ZXh0dHR7WzFdfSJdLFswLDAsIlxcdGV4dHR0eygpfSJdLFswLDEsIlxcdGV4dHR0eygpfSJdLFsxLDAsIlxcdGV4dHR0e1tdLFtdfSJdLFsxLDEsIlxcdGV4dHR0e1tdfSJdLFszLDAsIlxcdGV4dHR0e1syOzFdLFtdfSJdLFszLDEsIlxcdGV4dHR0e1sxOzJdfSJdLFswLDJdLFsxLDMsIiIsMCx7ImNvbG91ciI6WzAsNjAsNjBdfV0sWzQsNSwiIiwwLHsic3R5bGUiOnsiaGVhZCI6eyJuYW1lIjoibm9uZSJ9fX1dLFs0LDYsIiIsMCx7ImNvbG91ciI6WzAsNjAsNjBdfV0sWzUsN10sWzcsM10sWzYsMSwiIiwwLHsiY29sb3VyIjpbMCw2MCw2MF19XSxbNiw3XSxbOCwwXSxbOSwyLCIiLDAseyJjb2xvdXIiOlswLDYwLDYwXX1dLFsxLDhdLFszLDksIiIsMCx7ImNvbG91ciI6WzAsNjAsNjBdfV0sWzgsOV1d -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsMTAsWzQsMCwiXFx0ZXh0dHR7MSwoW10sWzJdKX0iXSxbMiwwLCJcXHRleHR0dHtbMV0sW119Il0sWzQsMSwiXFx0ZXh0dHR7MSxbMl19Il0sWzIsMSwiXFx0ZXh0dHR7WzFdfSJdLFswLDAsIlxcdGV4dHR0eygpfSJdLFswLDEsIlxcdGV4dHR0eygpfSJdLFsxLDAsIlxcdGV4dHR0e1tdLFtdfSJdLFsxLDEsIlxcdGV4dHR0e1tdfSJdLFszLDAsIlxcdGV4dHR0e1syOzFdLFtdfSJdLFszLDEsIlxcdGV4dHR0e1sxOzJdfSJdLFswLDJdLFsxLDMsIiIsMCx7ImNvbG91ciI6WzAsNjAsNjBdfV0sWzQsNSwiIiwwLHsic3R5bGUiOnsiaGVhZCI6eyJuYW1lIjoibm9uZSJ9fX1dLFs0LDYsIiIsMCx7ImNvbG91ciI6WzAsNjAsNjBdfV0sWzUsN10sWzcsM10sWzYsMSwiIiwwLHsiY29sb3VyIjpbMCw2MCw2MF19XSxbNiw3XSxbOCwwXSxbOSwyLCIiLDAseyJjb2xvdXIiOlswLDYwLDYwXX1dLFsxLDhdLFszLDksIiIsMCx7ImNvbG91ciI6WzAsNjAsNjBdfV0sWzgsOV1d&embed" width="750" height="250" style="border-radius: 8px; border: none;"></iframe>

Having proven the correctness of `BatchedQueue` relative to the specification `ListQueue`, let us now turn our attention to analyzing the cost of `BatchedQueue`.

# Cost annotations: cost reified as printing {#cost}

To analyze the cost of a program, we must pin down an intended cost model.
Rather than use a machine-dependent notion of cost, we can reify an abstract notion of cost into programs themselves.
This can be accomplished by annotating programs with a primitive, `charge`, that indicates which parts of a program are meant to be thought of as costly.
We may implement `charge` using printing, displaying `$` symbols at run-time when cost should be counted:
```ocaml
let charge (c : int) : unit = print_string (String.make c '$')
```
Evaluating `charge c` will print out `c` many `$` symbols, akin to incrementing a global counter by `c`.
We may now instrument our programs with this `charge` function wherever we wish to track cost.
Then, instead of using a stopwatch to time the execution of a program, we simply count the number of `$` symbols printed to determine the abstract cost spent.
Note that the use of `charge` does not otherwise impact the behavior of a computation.

In our running batched queue example, let us choose our cost model to be the number of recursive calls made; under this scheme, `List.rev inbox` should charge `List.length inbox` cost, as indicated in the modified code below.
```ocaml,hl_lines=12
module BatchedQueue : QUEUE with type t = int list * int list = struct
  type t = int list * int list

  let empty () = [], []

  let enqueue x (inbox, outbox) = x :: inbox, outbox

  let dequeue = function
    | inbox, x :: outbox -> x, (inbox, outbox)
    | inbox, [] ->
      (match
         charge (List.length inbox);
         List.rev inbox
       with
       | x :: outbox -> x, ([], outbox)
       | [] -> 0, ([], []))
  ;;
end
```

# Amortized analysis: aggregate cost analysis for data structures {#amortized-analysis}

Now, with a `charge`-annotated program, the problem of cost analysis can be posed precisely: how many `$` symbols does a given usage pattern of `BatchedQueue` print?

At first glance, the `BatchedQueue` implementation does not look particularly efficient.
Although we treat `empty` and `enqueue` as having zero cost, the worst-case cost incurred by `dequeue` is linear in the number of elements stored in the queue.
However, plotting the total cost of a sequence of queue operations reveals an important property.

<img src="./queue.png" alt="plot showing the total cost over time, which is always upper bounded by the total number of enqueue operations performed" style="display: block; margin-left: auto; margin-right: auto;">

Even though a linear, \\( n \\)-cost dequeue operation is possible, the frequency of such an operation is inversely proportional to \\( n \\).
In other words, we can only experience an operation that costs \\( n \\) once after every \\( n \\) enqueue operations.
Since the total cost of a sequence of operations involving \\( n \\) enqueues is at most \\( n \\), it's almost as though each operation is *constant-time*!
This observation was made by Sleator and Tarjan in their seminal work introducing the method of *amortized cost analysis* for data structures:

> In many uses of data structures, a *sequence of operations*, rather than just a single operation, is performed, and we are *interested in the total time of the sequence*, rather than in the times of the individual operations.
>
> <div style="text-align: right"> &ndash;Tarjan, 1985, <a href="https://epubs.siam.org/doi/10.1137/0606031">Amortized Computational Complexity</a> </div>

\\[
  \global\def\AC#1{\text{AC}({#1})}
  \global\def\C#1{\text{C}({#1})}
\\]

Using amortized analysis, we will show that each enqueue can be thought of as having a constant cost contribution in a sequence of operations.
Let \\( \AC{e} \\) represent the "abstract" amortized cost it would take to evaluate the operation \\( e \\) that computes an abstract, specification-level `ListQueue.t` state.
Then, for a queue represented by a list \\( l \\), we will show that
- the amortized cost of creating an empty batched queue is \\( \AC{\texttt{LQ.empty ()}} \coloneqq 0 \\),
- the amortized cost of each enqueue operation is \\( \AC{\texttt{LQ.enqueue}~x~l} \coloneqq 1 \\), and
- the amortized cost of each dequeue operation is \\( \AC{\texttt{LQ.dequeue}~l} \coloneqq 0 \\).

In other words, a client can imagine these costs when using the batched queue data structure, and while these costs may not be accurate "locally" (for each operation), they will be accurate "globally" (after a sequence of operations).

We now recall the physicist's method of amortized analysis, proposed by Sleator and described in the quoted work.
In this method, one gives a *potential function* \\( \Phi : \texttt{BQ.t} \to \mathbb{N} \\), describing the cost that a client of the batched queue data structure imagines has already occurred, according to the above amortized cost interface.
Then, each operation on a state \\( q \\) will have license to perform \\( \Phi(q) \\) cost more than what the interface states, since the client has already imagined paying this cost.

For our batched queue example, we may choose
\\[ \Phi(\textit{inbox}, \textit{outbox}) = \mathsf{length}(\textit{inbox}), \\]
since each a client would believe that one unit of cost has been charged for each element in the inbox list, even though the charge has not yet officially occurred.

The potential function must satisfy a property akin to the [law of conservation of energy](https://en.wikipedia.org/wiki/Conservation_of_energy), hence the term "potential": it must be the case (here, informally) that each operation satisfies
\\[ \text{AC} = \text{C} + \Phi^\prime - \Phi, \\]
where \\( \text{AC} \\) is the amortized cost of the operation, \\( \text{C} \\) is the true cost of the operation, \\( \Phi \\) is the potential of the state before the operation, and \\( \Phi^\prime \\) is the potential of the state after the operation.
Rephrased as
\\[ \Phi + \text{AC} = \text{C} + \Phi^\prime, \\]
this equation is exactly the conservation of energy, where the potentials \\( \Phi \\)/\\( \Phi^\prime \\) play the role of the potential energy of a physical system before/after a time elapses and the true/amortized cost play the role of the expended energy.

Let \\( \C{e} \\) represent be the cost associated with computing the result of the operation \\( e \\).
Formally, this amortization principle may be written as the following conditions on the function \\( \Phi \\), one per operation in the `QUEUE` interface:
1. \\( \AC{\texttt{LQ.empty ()}} = \C{\texttt{BQ.empty ()}} + \Phi(\texttt{BQ.empty ()}) \\);
2. \\( \AC{\texttt{LQ.enqueue}\ x~(\alpha~q)} = \C{\texttt{BQ.enqueue}\ x~q} + \Phi(\texttt{BQ.enqueue}\ x~q) - \Phi(q) \\); and
3. \\( \AC{\texttt{LQ.dequeue}\ (\alpha~q)} = \C{\texttt{BQ.dequeue}\ q} + \Phi^\prime(\texttt{BQ.dequeue}\ q) - \Phi(q) \\), where \\( \Phi^\prime(x, q^\prime) = \Phi(q^\prime) \\).

Iterating these equations, we may analyze the total cost of a sequence of operations using a [telescoping sum](https://en.wikipedia.org/wiki/Telescoping_series).
Let \\( q_i = f_i(f_{i-1}(\cdots(f_0(\texttt{empty ()})))) \\) be the \\(i^\text{th}\\) state in a sequence of states, where \\(f_i\\) is the state transition function underlying the \\(i^\text{th}\\) operation (either `dequeue`, dropping the dequeued element, or `enqueue`).
As a matter of notational convenience, let us write \\( \C{f_i(q_i)} \\) for the cost incurred by operation \\( f_i \\) on state \\( q_i \\).
As shown by Sleator and Tarjan, we can bound the total cost of a sequence of operations using the principle of amortization:
$$
  \begin{align*}
    n
      &\ge \sum_{i = 0}^{n - 1} \AC{f_i(\alpha~q_i)}  &\text{(each operation has amortized cost $0$ or $1$)} \\\\
      &= \sum_{i = 0}^{n - 1} \C{f_i(q_i)} + \Phi(f_i(q_i)) - \Phi(q)  &\text{(amortization principle)} \\\\
      &= \sum_{i = 0}^{n - 1} \C{f_i(q_i)} + \Phi(q_{i+1}) - \Phi(q)  &\text{(definition of $q_{i+1}$)} \\\\
      &= \Phi(q_n) - \Phi(q_0) + \sum_{i = 0}^{n - 1} \C{f_i(q_i)}  &\text{(telescoping sum)} \\\\
      &= \Phi(q_n) - \Phi(\texttt{empty ()}) + \sum_{i = 0}^{n - 1} \C{f_i(q_i)}  &\text{(definition of $q_0$)} \\\\
      &= \Phi(q_n) + \sum_{i = 0}^{n - 1} \C{f_i(q_i)}  &\text{(amortization principle for $\texttt{empty}$)} \\\\
      &\ge \sum_{i = 0}^{n - 1} \C{f_i(q_i)}
  \end{align*}
$$
We use the fact that the amortization condition for the `empty` operation ensures that \\( \C{\texttt{empty ()}} = \Phi(\texttt{empty ()}) = 0 \\).
In summary, the amortization principle ensures that the true total cost of a sequence of \\( n \\) operations is at most \\( n \\).


# Cost meets behavior: amortized analysis as a cost-aware abstraction function {#consolidation}

You may have smelled some similarities between [abstraction functions](#abstraction-function) and [potential functions](#amortized-analysis): both are functions with domain `BQ.t` that must satisfy three conditions, one per operation in the `QUEUE` interface.
Using this observation, we can exhibit the potential functions of amortized analysis as a first-class construct in our programming language.

First, notice that although cost was reified in `BatchedQueue` using the `charge` primitive, the amortized cost interface only existed at the level of an external mathematical analysis.
Since `ListQueue` already represented the intended behavior of a batched queue, we may as well annotate it with intended amortized costs; that way, client code can treat `ListQueue` as the mental model for `BatchedQueue`, including both behavior and amortized cost.
Since the only nonzero amortized cost was the \\( 1 \\) cost per enqueue, we annotate as follows:
```ocaml,hl_lines=7
module ListQueue : QUEUE with type t = int list = struct
  type t = int list

  let empty () = []

  let enqueue x l =
    charge 1;
    l @ [ x ]
  ;;

  let dequeue = function
    | [] -> 0, []
    | x :: l -> x, l
  ;;
end
```

In light of these cost-aware modifications to `BatchedQueue` and `ListQueue`, the existing function `alpha` no longer meets the criteria for being a valid abstraction function.
The criteria for an abstraction function require equalities between `BatchedQueue` and `ListQueue` operations, mediated by `alpha`; however, such equalities ought to now consider cost, but the expressions on either side of the equations do not always have the same costs.
For example, [we asked](#abstraction-function) that \\[ \alpha(\texttt{BQ.enqueue}\ x~q) = \texttt{LQ.enqueue}\ x~(\alpha~q), \\] again writing \\( \alpha \\) for the abstraction function, `alpha`.
While both sides still return the same results, we now have that the left side charges for zero cost (in `BQ.enqueue`), even though the right side claims to charge for one unit of cost (in `LQ.enqueue`).
To rectify this issue without changing the enqueue implementations, there's only one possible solution: make the `alpha` function itself charge some cost!
If \\( \alpha(\texttt{BQ.enqueue}\ x~q) \\) were to charge \\( c + 1 \\) units of cost and \\( \alpha~q \\) were to charge \\( c \\) units, for any number \\( c \\), the cost of both sides of the equation would balance:
\\[ 0 + {\color{red}(c + 1)} = {\color{red}c} + 1, \\]
summing the costs from the components of each side of the abstraction function equation and marking the cost from the abstraction function \\( \alpha \\) in \\( \color{red}\text{red} \\).

Let's make this a bit more precise.
If the abstraction function were to incur some amount of cost when applied to a given \\( q \\), which we write \\( \C{\alpha~q} \\), the following condition would have to hold for the enqueue operation:
\\[ \C{\texttt{BQ.enqueue}\ x~q} + \C{\alpha(\texttt{BQ.enqueue}\ x~q)} = \C{\alpha~q} + \C{\texttt{LQ.enqueue}\ x~(\alpha~q)} \\]
Since we included the amortized cost specification in `ListQueue`, we have \\[ \C{\texttt{LQ.enqueue}\ x~(\alpha~q)} \coloneqq \AC{\texttt{LQ.enqueue}\ x~(\alpha~q)} \\] by definition.

Now, if we compute the cost of the abstraction function as the potential function, \\( \C{\alpha~q} \coloneqq \Phi(q) \\), **the cost aspect of the abstraction function condition is precisely the amortization condition**!
\\[ \C{\texttt{BQ.enqueue}\ x~q} + \Phi(\texttt{BQ.enqueue}\ x~q) = \Phi(q) + \AC{\texttt{LQ.enqueue}\ x~(\alpha~q)} \\]
In other words: a *cost-aware abstraction function* is a *behavioral abstraction function* equipped with cost according to an amortized analysis *potential function*.

Let's see how this looks in practice.
We can annotate the abstraction function itself with cost, according to the potential function \\( \Phi(\textit{inbox}, \textit{outbox}) = \mathsf{length}(\textit{inbox}) \\) from before:
```ocaml,hl_lines=3
let alpha : BatchedQueue.t -> ListQueue.t =
  fun (inbox, outbox) ->
  charge (List.length inbox);
  outbox @ List.rev inbox
;;
```
This abstraction function integrates cost and behavior considerations, both charging according to the potential function and converting a `BatchedQueue.t` representation to a `ListQueue.t` representation.
The amortization conditions are exactly verified by the [abstraction function criteria](#abstraction-function).
Let's briefly sketch the proofs for `empty` and `enqueue` as follows.
First, `alpha` preserves `empty`, including cost:
```ocaml,hl_lines=3
alpha (BatchedQueue.empty ())
= alpha ([], [])
= charge 0; []
= []
= ListQueue.empty ()
```
The proof is the same as [before](#abstraction-function), but with one extra step to remove the inconsequential `charge 0` from the definition of `alpha`.
Next, `alpha` preserves `enqueue`:
```ocaml,hl_lines=3-5 7
alpha (BatchedQueue.enqueue x (inbox, outbox))
= alpha (x :: inbox, outbox)
= charge (List.length (x :: inbox)); outbox @ List.rev (x :: inbox)
= charge (1 + List.length inbox); outbox @ List.rev (x :: inbox)
= charge 1; charge (List.length inbox); outbox @ List.rev (x :: inbox)
= charge 1; charge (List.length inbox); outbox @ List.rev inbox @ [ x ]
= charge 1; (charge (List.length inbox); outbox @ List.rev inbox) @ [ x ]
= charge 1; alpha (inbox, outbox) @ [ x ]
= ListQueue.enqueue x (alpha (inbox, outbox))
```
The highlighted lines show differences compared to the proofs sans cost.
In addition to converting the efficient batched representation to the specification-level list representation, the abstraction function releases the "potential" associated with the `inbox` list.
Since `BatchedQueue.enqueue` prepends `x` to `inbox`, the `alpha` function charges `1 + List.length inbox`, where the `1` corresponds to the `1` cost charged by the `ListQueue.enqueue` cost specification and the remaining `List.length inbox` is preserved.

Viewing amortized analysis as a cost-aware abstraction function proof, the reasoning principles afforded by abstraction functions are upgraded to the cost-aware setting accordingly.
For example, as before, we can switch from using `BatchedQueue` to using `ListQueue` at any point in a sequence of operations and the results will cohere, including the cost (*i.e.*, the number of `$` symbols printed):
```ocaml,hl_lines=4-6
let demo =
  BQ.empty ()            (* $0 *)
  |> BQ.enqueue 1        (* $0 *)
  (* ⬆️ batched queue *)
  |> alpha               (* $1 *)
  (* ⬇️ list queue *)
  |> LQ.enqueue 2        (* $1 *)
  |> LQ.dequeue          (* $0 *)
;;
```
Regardless of the placement of the switch using `alpha`, the total cost of this sequence of operations will be `$2`.
We can again visualize this process as the composition of commutative squares:
<!-- https://q.uiver.app/#q=WzAsMTAsWzQsMCwiXFx0ZXh0dHR7aW50fSBcXGFzdCBcXHRleHR0dHtCUS50fSJdLFsyLDAsIlxcdGV4dHR0e0JRLnR9Il0sWzQsMSwiXFx0ZXh0dHR7aW50fSBcXGFzdCBcXHRleHR0dHtMUS50fSJdLFsyLDEsIlxcdGV4dHR0e0xRLnR9Il0sWzAsMCwiXFx0ZXh0dHR7dW5pdH0iXSxbMCwxLCJcXHRleHR0dHt1bml0fSJdLFsxLDAsIlxcdGV4dHR0e0JRLnR9Il0sWzEsMSwiXFx0ZXh0dHR7TFEudH0iXSxbMywwLCJcXHRleHR0dHtCUS50fSJdLFszLDEsIlxcdGV4dHR0e0xRLnR9Il0sWzAsMiwiXFxhbHBoYSciXSxbMSwzLCJcXGFscGhhIiwwLHsiY29sb3VyIjpbMCw2MCw2MF19LFswLDYwLDYwLDFdXSxbNCw1LCIiLDAseyJzdHlsZSI6eyJoZWFkIjp7Im5hbWUiOiJub25lIn19fV0sWzQsNiwiXFx0ZXh0dHR7ZW1wdHl9IiwwLHsiY29sb3VyIjpbMCw2MCw2MF19LFswLDYwLDYwLDFdXSxbNSw3LCJcXHRleHR0dHtlbXB0eX0iLDJdLFs3LDMsIlxcdGV4dHR0e2VucXVldWV9fjEiLDJdLFs2LDEsIlxcdGV4dHR0e2VucXVldWV9fjEiLDAseyJjb2xvdXIiOlswLDYwLDYwXX0sWzAsNjAsNjAsMV1dLFs2LDcsIlxcYWxwaGEiXSxbOCwwLCJcXHRleHR0dHtkZXF1ZXVlfSJdLFs5LDIsIlxcdGV4dHR0e2RlcXVldWV9IiwyLHsiY29sb3VyIjpbMCw2MCw2MF19LFswLDYwLDYwLDFdXSxbMSw4LCJcXHRleHR0dHtlbnF1ZXVlfX4yIl0sWzMsOSwiXFx0ZXh0dHR7ZW5xdWV1ZX1+MiIsMix7ImNvbG91ciI6WzAsNjAsNjBdfSxbMCw2MCw2MCwxXV0sWzgsOSwiXFxhbHBoYSJdXQ== -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsMTAsWzQsMCwiXFx0ZXh0dHR7aW50fSBcXGFzdCBcXHRleHR0dHtCUS50fSJdLFsyLDAsIlxcdGV4dHR0e0JRLnR9Il0sWzQsMSwiXFx0ZXh0dHR7aW50fSBcXGFzdCBcXHRleHR0dHtMUS50fSJdLFsyLDEsIlxcdGV4dHR0e0xRLnR9Il0sWzAsMCwiXFx0ZXh0dHR7dW5pdH0iXSxbMCwxLCJcXHRleHR0dHt1bml0fSJdLFsxLDAsIlxcdGV4dHR0e0JRLnR9Il0sWzEsMSwiXFx0ZXh0dHR7TFEudH0iXSxbMywwLCJcXHRleHR0dHtCUS50fSJdLFszLDEsIlxcdGV4dHR0e0xRLnR9Il0sWzAsMiwiXFxhbHBoYSciXSxbMSwzLCJcXGFscGhhIiwwLHsiY29sb3VyIjpbMCw2MCw2MF19LFswLDYwLDYwLDFdXSxbNCw1LCIiLDAseyJzdHlsZSI6eyJoZWFkIjp7Im5hbWUiOiJub25lIn19fV0sWzQsNiwiXFx0ZXh0dHR7ZW1wdHl9IiwwLHsiY29sb3VyIjpbMCw2MCw2MF19LFswLDYwLDYwLDFdXSxbNSw3LCJcXHRleHR0dHtlbXB0eX0iLDJdLFs3LDMsIlxcdGV4dHR0e2VucXVldWV9fjEiLDJdLFs2LDEsIlxcdGV4dHR0e2VucXVldWV9fjEiLDAseyJjb2xvdXIiOlswLDYwLDYwXX0sWzAsNjAsNjAsMV1dLFs2LDcsIlxcYWxwaGEiXSxbOCwwLCJcXHRleHR0dHtkZXF1ZXVlfSJdLFs5LDIsIlxcdGV4dHR0e2RlcXVldWV9IiwyLHsiY29sb3VyIjpbMCw2MCw2MF19LFswLDYwLDYwLDFdXSxbMSw4LCJcXHRleHR0dHtlbnF1ZXVlfX4yIl0sWzMsOSwiXFx0ZXh0dHR7ZW5xdWV1ZX1+MiIsMix7ImNvbG91ciI6WzAsNjAsNjBdfSxbMCw2MCw2MCwxXV0sWzgsOSwiXFxhbHBoYSJdXQ==&embed" width="750" height="250" style="border-radius: 8px; border: none;"></iframe>

The [telescoping sum of amortized analysis](#amortized-analysis) is hidden within this composition: rather than add a potential and immediately subtract it afterwards, the overlaying of adjacent uses of \\( \alpha \\) ensures that the intermediate potentials do not contribute to the global tally, computed by the outer edges of the larger rectangle built out of the individual squares.
For this particular trace, we can view the data as before, annotating arrows with their associated cost:
<!-- https://q.uiver.app/#q=WzAsMTAsWzQsMCwiXFx0ZXh0dHR7MSwoW10sWzJdKX0iXSxbMiwwLCJcXHRleHR0dHtbMV0sW119Il0sWzQsMSwiXFx0ZXh0dHR7MSxbMl19Il0sWzIsMSwiXFx0ZXh0dHR7WzFdfSJdLFswLDAsIlxcdGV4dHR0eygpfSJdLFswLDEsIlxcdGV4dHR0eygpfSJdLFsxLDAsIlxcdGV4dHR0e1tdLFtdfSJdLFsxLDEsIlxcdGV4dHR0e1tdfSJdLFszLDAsIlxcdGV4dHR0e1syOzFdLFtdfSJdLFszLDEsIlxcdGV4dHR0e1sxOzJdfSJdLFswLDJdLFsxLDMsIiQiLDAseyJjb2xvdXIiOlswLDYwLDYwXX0sWzAsNjAsNjAsMV1dLFs0LDUsIiIsMCx7InN0eWxlIjp7ImhlYWQiOnsibmFtZSI6Im5vbmUifX19XSxbNCw2LCIiLDAseyJjb2xvdXIiOlswLDYwLDYwXX1dLFs1LDddLFs3LDMsIiQiLDJdLFs2LDEsIiIsMCx7ImNvbG91ciI6WzAsNjAsNjBdfV0sWzYsN10sWzgsMCwiJCQiXSxbOSwyLCIiLDIseyJjb2xvdXIiOlswLDYwLDYwXX1dLFsxLDhdLFszLDksIiQiLDIseyJjb2xvdXIiOlswLDYwLDYwXX0sWzAsNjAsNjAsMV1dLFs4LDksIiQkIl1d -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsMTAsWzQsMCwiXFx0ZXh0dHR7MSwoW10sWzJdKX0iXSxbMiwwLCJcXHRleHR0dHtbMV0sW119Il0sWzQsMSwiXFx0ZXh0dHR7MSxbMl19Il0sWzIsMSwiXFx0ZXh0dHR7WzFdfSJdLFswLDAsIlxcdGV4dHR0eygpfSJdLFswLDEsIlxcdGV4dHR0eygpfSJdLFsxLDAsIlxcdGV4dHR0e1tdLFtdfSJdLFsxLDEsIlxcdGV4dHR0e1tdfSJdLFszLDAsIlxcdGV4dHR0e1syOzFdLFtdfSJdLFszLDEsIlxcdGV4dHR0e1sxOzJdfSJdLFswLDJdLFsxLDMsIiQiLDAseyJjb2xvdXIiOlswLDYwLDYwXX0sWzAsNjAsNjAsMV1dLFs0LDUsIiIsMCx7InN0eWxlIjp7ImhlYWQiOnsibmFtZSI6Im5vbmUifX19XSxbNCw2LCIiLDAseyJjb2xvdXIiOlswLDYwLDYwXX1dLFs1LDddLFs3LDMsIiQiLDJdLFs2LDEsIiIsMCx7ImNvbG91ciI6WzAsNjAsNjBdfV0sWzYsN10sWzgsMCwiJCQiXSxbOSwyLCIiLDIseyJjb2xvdXIiOlswLDYwLDYwXX1dLFsxLDhdLFszLDksIiQiLDIseyJjb2xvdXIiOlswLDYwLDYwXX0sWzAsNjAsNjAsMV1dLFs4LDksIiQkIl1d&embed" width="750" height="250" style="border-radius: 8px; border: none;"></iframe>

The true costs are rendered along the top edge; the specified amortized costs are rendered along the bottom edge; and the potential according to the potential function is shown on the vertical edges.
Each component square has the same cost associated with both of its paths, and all paths from the top-left corner to the bottom-right corner carry two units of cost, `$$`.

# Conclusion {#conclusion}

In this post, we observed that a potential function used in amortized analysis is precisely the cost incurred by an abstraction function in a setting where cost is reified in programs.
Beyond the inherent conceptual benefit of consolidation of ideas, viewing amortized analysis in this way also appears to be immensely practical: when verifying batched queues in [Calf](https://dl.acm.org/doi/abs/10.1145/3498670), the abstraction function perspective reduced the size of the verification from 700 lines of code down to 100 lines.
Moreover, this perspective on amortized analysis is compatible with programming languages for automated resource analysis, such as [AARA](https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science/article/two-decades-of-automatic-amortized-resource-analysis/9A47A8663CD8A7147E2F17865C368094).

While we considered the relatively simple example of batched queues here, the story generalizes to more complex scenarios, such as situations when the amortized cost described is an upper bound only on the true cost (in analogy with physics, data structures that sometimes experience "energy loss").

Throughout this development, we used the `charge` primitive, viewing cost as a particular form of printing.
Although we only ever printed the `$` symbol, the approach discussed here scales to arbitrary printing.
For example, in [the paper](https://entics.episciences.org/14797), we observe that buffered string printing can be framed as amortization, where the potential function serves to flush the buffer.
