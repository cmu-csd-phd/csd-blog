+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "Amortized Analysis as a Cost-Aware Abstraction Function"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2025-04-03

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
    {name = "Harry Q. Bovik", url = "http://www.cs.cmu.edu/~bovik/"},
    {name = "Committee Member 2's Full Name", url = "Committee Member 2's page"},
    {name = "Committee Member 3's Full Name", url = "Committee Member 3's page"}
]
+++


Amortized analysis is a cost analysis technique for data structures in which cost is studied in aggregate: rather than considering the maximum cost of a single operation, one bounds the total cost encountered throughout a session.
The semantics of data structures, on the other hand, has long been studied using the notion of abstraction functions, which translate concrete data structure representations into a semantic representation.
In this post, I will demonstrate how to unify these two techniques, packaging the data associated with an amortized analysis as a cost-aware abstraction function.
This reframing is more amenable to formal verification, consolidates prior variations of amortized analysis, and generalizes amortization to novel settings.
This work was published at [MFPS 2024](https://entics.episciences.org/14797).


# Motivating example: batched queues {#batched-queue}

As a running example, let us consider the [queue](https://en.wikipedia.org/wiki/Queue_(abstract_data_type)) abstract data type, which describes finite lists of data that can be "enqueued" to and "dequeued" from in a first-in, first-out manner.
This description of operations can be given the following types:
```ocaml
module type QUEUE = sig
  type t

  val empty : unit -> t
  val enqueue : int -> t -> t
  val dequeue : t -> int * t
end
```
To implement `QUEUE`, we must choose a representation type `t`, provide an empty queue of type `t`, and implement the `enqueue` and `dequeue` operations on type `t`.
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
The empty queue is represented as the empty list `[]`; enqueueing `x` appends the singleton list `[ x ]`; and dequeueing pattern matches on the given list (either empty `[]` or nonempty `x :: l`), returning `0` as a default element when the queue is empty.
We can run a simple test case to check the behavior of this code as follows:
```ocaml
let demo =
  let module Q = ListQueue in
  let q = Q.empty () in
  let q = Q.enqueue 1 q in
  let q = Q.enqueue 2 q in
  let q = Q.enqueue 3 q in
  let n1, q = Q.dequeue q in
  let n2, q = Q.dequeue q in
  let n3, _ = Q.dequeue q in
  n1, n2, n3
;;
```
Here, letting `Q` be an alisa for `ListQueue`, we start with the empty queue `Q.empty ()`; enqueue the numbers `1`, `2`, `3`; and then dequeue from the queue three times.
Indeed, the dequeued results `n1, n2, n3` are `1, 2, 3`, as expected.

While this implementation clearly conveys the intended behavior of a queue, it lacks in efficiency: the implementation of the enqueue operation takes linear time in the length of the list `l` representing the queue.
Therefore, it is best to treat this implementation as a specification only, describing how a more efficient queue ought to be implemented.

For an alternative implementation, sometimes referred to as a [batched queue](https://en.wikipedia.org/wiki/Queue_(abstract_data_type)#Amortized_queue), we can choose the representation type to be pairs of lists, `t = int list * int list`.
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
Every queue state is now a pair of lists `inbox, outbox`, where the inbox list is in reverse order.
A queue can now have more than one representation; for example, the queue `[1; 2; 3]` can be represented as
- `[], [1; 2; 3]`,
- `[3], [1; 2]`,
- `[3; 2], [1]`, and
- `[3; 2; 1], []`.

The empty queue starts with both the inbox and outbox being empty, and the enqueue operation simply adds the new element `x` to the inbox.
The implementation of the dequeue operation is more complex:
1. In case the outbox is nonempty (*i.e.*, of the form `x :: outbox`), we dequeue this element `x`, leaving the inbox alone and updating the outbox to the remaining outbox from this list.
2. If the outbox is empty, we reverse the inbox and treat it as the new outbox. Then, we attempt to take the first element from this new outbox. If the inbox was also empty, we return default element `0` and leave both the inbox and the outbox empty.

Compared to `ListQueue`, it is less obvious that `BatchedQueue` correctly implements the queue abstraction.
We can run the same test case before as a simple check, swapping `ListQueue` for `BatchedQueue`:
```ocaml
let demo =
  let module Q = BatchedQueue in
  let q = Q.empty () in
  let q = Q.enqueue 1 q in
  let q = Q.enqueue 2 q in
  let q = Q.enqueue 3 q in
  let n1, q = Q.dequeue q in
  let n2, q = Q.dequeue q in
  let n3, _ = Q.dequeue q in
  n1, n2, n3
;;
```
As before, the result is `1, 2, 3`.
How can we prove that this will always be the case, though?
Let's discuss the proof technique that shows how we can verify the correctness of `BatchedQueue` relative to `ListQueue`.
Then, we can analyze the cost of `BatchedQueue`.


# Abstraction functions {#abstraction-function}

To verify that `BatchedQueue` is correct relative to the specification `ListQueue`, we use an *abstraction function* that converts a batched queue state to a single list representing the same state.
This venerable idea goes back to Tony Hoare:

> The first requirement for the proof [of correctness] is to define the relationship between the abstract space in which the abstract program is written, and the space of the concrete representation.
> This can be accomplished by giving a function [\\( \alpha \\)] which maps the concrete variables into the abstract object which they represent.
> Note that in this and in many other cases [\\( \alpha \\)] will be a many-one function.
> Thus there is no unique concrete value representing any abstract one.
> <div style="text-align: right"> &ndash;Hoare, 1972, <a href="https://dl.acm.org/doi/abs/10.5555/63445.C1104363">Proof of Correctness of Data Representations</a> </div>

For our example, we can implement the abstraction function as follows, rendering \\( \alpha \\) as `abstraction` in code:
```ocaml
let abstraction : BatchedQueue.t -> ListQueue.t =
  fun (inbox, outbox) -> outbox @ List.rev inbox
;;
```
We turn `inbox, outbox` into a single list by appending the reversed `inbox` list to the `outbox` list.
For example, the pair `[3; 2], [1]` will be mapped by the `abstraction` function to the list `[1; 2; 3]`.

Now, to verify the operations are correct, we must show that the `BatchedQueue` operations cohere with the simpler `ListQueue` operations, mediated by this function, `abstraction`.
In mathematics, this is called showing that `abstraction` is a *`QUEUE`-homomorphism*.
Concretely, this means checking the following conditions, one per operation in the `QUEUE` interface:
1. `abstraction (BatchedQueue.empty ())` = `ListQueue.empty ()`,
2. `abstraction (BatchedQueue.enqueue x q)` = `ListQueue.enqueue x (abstraction q)` for all `q : BatchedQueue.t`, and
3. `abstraction' (BatchedQueue.dequeue q)` = `ListQueue.dequeue (abstraction q)` for all `q : BatchedQueue.t`, where `abstraction' = fun (x, q') -> (x, abstraction q')` applies the `abstraction` function to the second component of a pair `int * BatchedQueue.t`.

These conditions can be visualized using the following diagrams, abbreviating `BatchedQueue` as `BQ` and `ListQueue` as `LQ`.
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
<!-- https://q.uiver.app/#q=WzAsNCxbMSwwLCJcXHRleHR0dHtpbnR9IFxcYXN0IFxcdGV4dHR0e0JRLnR9Il0sWzAsMCwiXFx0ZXh0dHR7QlEudH0iXSxbMSwxLCJcXHRleHR0dHtpbnR9IFxcYXN0IFxcdGV4dHR0e0JRLnR9Il0sWzAsMSwiXFx0ZXh0dHR7TFEudH0iXSxbMCwyLCJcXGFscGhhJyJdLFsxLDAsIlxcdGV4dHR0e0JRLmRlcXVldWV9Il0sWzMsMiwiXFx0ZXh0dHR7TFEuZGVxdWV1ZX0iLDJdLFsxLDMsIlxcYWxwaGEiXV0= -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsNCxbMSwwLCJcXHRleHR0dHtpbnR9IFxcYXN0IFxcdGV4dHR0e0JRLnR9Il0sWzAsMCwiXFx0ZXh0dHR7QlEudH0iXSxbMSwxLCJcXHRleHR0dHtpbnR9IFxcYXN0IFxcdGV4dHR0e0JRLnR9Il0sWzAsMSwiXFx0ZXh0dHR7TFEudH0iXSxbMCwyLCJcXGFscGhhJyJdLFsxLDAsIlxcdGV4dHR0e0JRLmRlcXVldWV9Il0sWzMsMiwiXFx0ZXh0dHR7TFEuZGVxdWV1ZX0iLDJdLFsxLDMsIlxcYWxwaGEiXV0=&embed" width="300" height="250" style="border-radius: 8px; border: none;"></iframe>
  </div>
</div>

In fact, these conditions do hold, which we sketch the proofs of as follows.
First, `abstraction` preserves `empty`:
```
  abstraction (BatchedQueue.empty ())
= abstraction ([], [])
= []
= ListQueue.empty ()
```
Next, `abstraction` preserves `enqueue`
```
  abstraction (BatchedQueue.enqueue x (inbox, outbox))
= abstraction (x :: inbox, outbox)
= outbox @ List.rev (x :: inbox)
= outbox @ List.rev inbox @ [ x ]
= abstraction (inbox, outbox) @ [ x ]
= ListQueue.enqueue x (abstraction (inbox, outbox))
```
We omit the proof that `abstraction` preserves `dequeue`, which goes by cases.

Observe that the conditions can be combined to relate the results of sequences of operations.
In our sample trace, we may apply `abstraction` between any two operations, and the result will be unaffected; for example, we may place `abstraction` before the final dequeue as follows, using `BatchedQueue` before this point and `ListQueue` after this point.
```ocaml,hl_lines=9-12
let demo =
  let module Q = BatchedQueue in
  let q = Q.empty () in
  let q = Q.enqueue 1 q in
  let q = Q.enqueue 2 q in
  let q = Q.enqueue 3 q in
  let n1, q = Q.dequeue q in
  let n2, q = Q.dequeue q in
  (* ⬆️ batched queue *)
  let module Q = ListQueue in
  let q = abstraction q in
  (* ⬇️ list queue *)
  let n3, _ = Q.dequeue q in
  n1, n2, n3
;;
```

Diagrammatically, such equivalences are visualized as horizontal juxtaposition of commutative squares (omitting `BQ` and `LQ` on operation names and doing the smaller example of `dequeue (enqueue x (empty ()))` for space):

<!-- https://q.uiver.app/#q=WzAsOCxbMywwLCJcXHRleHR0dHtpbnR9IFxcYXN0IFxcdGV4dHR0e0JRLnR9Il0sWzIsMCwiXFx0ZXh0dHR7QlEudH0iXSxbMywxLCJcXHRleHR0dHtpbnR9IFxcYXN0IFxcdGV4dHR0e0JRLnR9Il0sWzIsMSwiXFx0ZXh0dHR7TFEudH0iXSxbMCwwLCJcXHRleHR0dHt1bml0fSJdLFswLDEsIlxcdGV4dHR0e3VuaXR9Il0sWzEsMCwiXFx0ZXh0dHR7QlEudH0iXSxbMSwxLCJcXHRleHR0dHtMUS50fSJdLFswLDIsIlxcYWxwaGEnIl0sWzEsMCwiXFx0ZXh0dHR7ZGVxdWV1ZX0iXSxbMywyLCJcXHRleHR0dHtkZXF1ZXVlfSIsMl0sWzEsMywiXFxhbHBoYSJdLFs0LDUsIiIsMCx7InN0eWxlIjp7ImhlYWQiOnsibmFtZSI6Im5vbmUifX19XSxbNCw2LCJcXHRleHR0dHtlbXB0eX0iXSxbNSw3LCJcXHRleHR0dHtlbXB0eX0iLDJdLFs3LDMsIlxcdGV4dHR0e2VucXVldWUgeH0iLDJdLFs2LDEsIlxcdGV4dHR0e2VucXVldWUgeH0iXSxbNiw3LCJcXGFscGhhIl1d -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsOCxbMywwLCJcXHRleHR0dHtpbnR9IFxcYXN0IFxcdGV4dHR0e0JRLnR9Il0sWzIsMCwiXFx0ZXh0dHR7QlEudH0iXSxbMywxLCJcXHRleHR0dHtpbnR9IFxcYXN0IFxcdGV4dHR0e0JRLnR9Il0sWzIsMSwiXFx0ZXh0dHR7TFEudH0iXSxbMCwwLCJcXHRleHR0dHt1bml0fSJdLFswLDEsIlxcdGV4dHR0e3VuaXR9Il0sWzEsMCwiXFx0ZXh0dHR7QlEudH0iXSxbMSwxLCJcXHRleHR0dHtMUS50fSJdLFswLDIsIlxcYWxwaGEnIl0sWzEsMCwiXFx0ZXh0dHR7ZGVxdWV1ZX0iXSxbMywyLCJcXHRleHR0dHtkZXF1ZXVlfSIsMl0sWzEsMywiXFxhbHBoYSJdLFs0LDUsIiIsMCx7InN0eWxlIjp7ImhlYWQiOnsibmFtZSI6Im5vbmUifX19XSxbNCw2LCJcXHRleHR0dHtlbXB0eX0iXSxbNSw3LCJcXHRleHR0dHtlbXB0eX0iLDJdLFs3LDMsIlxcdGV4dHR0e2VucXVldWUgeH0iLDJdLFs2LDEsIlxcdGV4dHR0e2VucXVldWUgeH0iXSxbNiw3LCJcXGFscGhhIl1d&embed" width="647" height="304" style="border-radius: 8px; border: none;"></iframe>

Having proven the correctness of `BatchedQueue` relative to the specification `ListQueue`, let us now turn our attention to analyzing the cost of `BatchedQueue`.

# Cost as an effect {#cost}

To analyze the cost of a program, we must pin down an intended cost model.
We may reify the choice of cost model within our code as a printing effect, as in [Calf](https://dl.acm.org/doi/abs/10.1145/3498670):
```ocaml
let charge (c : int) : unit = print_string (String.make c '$')
```
Evaluating `charge c` will print out `c` many `$` symbols, akin to incrementing a global counter by `c`.
We may now instrument our programs with this `charge` function wherever we wish to track cost.

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

Now, the problem of cost analysis can be posed precisely: how many `$` symbols does a given usage pattern of `BatchedQueue` print?


# Amortized analysis: aggregate cost analysis for data structures {#amortized-analysis}

At first glance, the `BatchedQueue` implementation does not look particularly efficient.
Although we treat `empty` and `enqueue` as having zero cost, the worst-case cost incurred by `dequeue` is linear in the number of elements stored in the queue.
However, plotting the total cost of a sequence of queue operations reveals an important property:

<img src="./queue.png" alt="plot showing the total cost over time, which is always upper bounded by the total number of enqueue operations performed" style="display: block; margin-left: auto; margin-right: auto;">

Even though a linear, \\( n \\)-cost dequeue operation is possible, the frequency of such an operation is inversely proportional to \\( n \\).
In other words, we can only experience an operation that costs \\( n \\) once after every \\( n \\) enqueue operations.
Since the total cost of a sequence of operations involving \\( n \\) enqueues is at most \\( n \\), it's almost as though each operation is *constant-time*!
This observation was made by Tarjan in his seminal paper introducing the method of *amortized cost analysis* for data structures:

> In many uses of data structures, a *sequence of operations*, rather than just a single operation, is performed, and we are *interested in the total time of the sequence*, rather than in the times of the individual operations.
>
> <div style="text-align: right"> &ndash;Tarjan, 1985, <a href="https://epubs.siam.org/doi/10.1137/0606031">Amortized Computational Complexity</a> </div>

Using amortized analysis, we will show that
- the amortized cost of creating an empty batched queue is \\( (\texttt{empty ()})^\text{AC} \coloneqq 0 \\),
- the amortized cost of each enqueue operation is \\( (\texttt{enqueue x q})^\text{AC} \coloneqq 1 \\), and
- the amortized cost of each dequeue operation is \\( (\texttt{dequeue q})^\text{AC} \coloneqq 0 \\).

In other words, a client can imagine these costs when using the batched queue data structure, and while these costs may not be accurate "locally" (for each operation), they will be accurate "globally" (after a sequence of operations).

We now recall the physicist's method of amortized analysis, proposed by Sleator and described in *op. cit*.
In this method, one gives a *potential function* \\( \Phi : \texttt{BQ.t} \to \mathbb{N} \\), describing the cost that a client of the batched queue data structure imagines has already occurred, according to the above amortized cost interface.
Then, each operation on a state \\( \texttt{q} \\) will have license to perform \\( \Phi(\texttt{q}) \\) cost more than what the interface states, since the client has already imagined paying this cost.

For our batched queue example, we may choose
\\[ \Phi(\textit{inbox}, \textit{outbox}) = \mathsf{length}(\textit{inbox}), \\]
since each a client would believe that one unit of cost has been charged for each element in the inbox list, even though the charge has not yet officially occurred.

The potential function must satisfy a property akin to the [law of conservation of energy](https://en.wikipedia.org/wiki/Conservation_of_energy), hence the term "potential": it must be the case (here, informally) that each operation satisfies
\\[ \text{AC} = \text{C} + \Phi' - \Phi, \\]
where \\( \text{AC} \\) is the amortized cost of the operation, \\( \text{C} \\) is the true cost of the operation, \\( \Phi \\) is the potential of the state before the operation, and \\( \Phi' \\) is the potential of the state after the operation.
Rephrased as
\\[ \Phi + \text{AC} = \text{C} + \Phi', \\]
this equation is exactly the conservation of energy, where the potentials \\( \Phi \\)/\\( \Phi' \\) play the role of the potential energy of a physical system before/after a time elapses and the true/amortized cost play the role of the kinetic energy.

Formally, this amortization principle may be written as the following conditions on the function \\( \Phi \\), one per operation in the `QUEUE` interface:
1. \\( (\texttt{empty ()})^\text{AC} = (\texttt{empty ()})^\text{C} + \Phi(\texttt{empty ()}) \\), *i.e.* \\( (\texttt{empty ()})^\text{C} = \Phi(\texttt{empty ()}) = 0 \\);
2. \\( (\texttt{enqueue x q})^\text{AC} = (\texttt{enqueue x q})^\text{C} + \Phi(\texttt{enqueue x q}) - \Phi(\texttt{q}) \\); and
3. \\( (\texttt{dequeue q})^\text{AC} = (\texttt{dequeue q})^\text{C} + \Phi'(\texttt{dequeue q}) - \Phi(\texttt{q}) \\), where \\( \Phi'(\texttt{x, q'}) = \Phi(\texttt{q'}) \\).

Iterating these equations, we may analyze the total cost of a sequence of operations using a [telescoping sum](https://en.wikipedia.org/wiki/Telescoping_series).
Let \\( q_i = f_i(f_{i-1}(\cdots(f_0(\texttt{empty ()})))) \\) be the \\(i^\text{th}\\) state in a sequence of states, where \\(f_i\\) is the state transition function underlying the \\(i^\text{th}\\) operation (either `dequeue`, dropping the dequeued element, or `enqueue`).
As shown by Tarjan, we can bound the total cost of a sequence of operations using the principle of amortization:
$$
  \begin{align*}
    n
      &\ge \sum_{i = 0}^{n - 1} f_i(q_i)^\text{AC}  &\text{(each operation costs $0$ or $1$)} \\\\
      &= \sum_{i = 0}^{n - 1} f_i(q_i)^\text{C} + \Phi(f_i(q_i)) - \Phi(q)  &\text{(amortization principle)} \\\\
      &= \sum_{i = 0}^{n - 1} f_i(q_i)^\text{C} + \Phi(q_{i+1}) - \Phi(q)  &\text{(definition of $q_{i+1}$)} \\\\
      &= \Phi(q_n) - \Phi(\texttt{empty ()}) + \sum_{i = 0}^{n - 1} f_i(q_i)^\text{C}  &\text{(telescoping sum)} \\\\
      &= \Phi(q_n) + \sum_{i = 0}^{n - 1} f_i(q_i)^\text{C}  &\text{(amortization principle for $\texttt{empty}$)} \\\\
      &\ge \sum_{i = 0}^{n - 1} f_i(q_i)^\text{C}
  \end{align*}
$$

In other words, the amortization principle ensures that the true total cost of a sequence of \\( n \\) operations is at most \\( n \\).


# Tarjan meets Hoare: amortized analysis as a cost-aware abstraction function {#consolidation}

You may have smelled some similarities between [abstraction functions](#abstraction-function) and [potential functions](#amortized-analysis): both are functions with domain `BQ.t` that must satisfy three conditions, one per operation in the `QUEUE` interface.
Using this observation, we can exhibit the potential functions of amortized analysis as a first-class construct in our programming language.

First, notice that although cost was reified in `BatchedQueue` using the `charge` effect, the amortized cost interface only existed at the level of mathematics.
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
As given, though, `abstraction` is no longer a valid abstraction function, including the `charge` effect!
For example, [we asked](#abstraction-function) that `abstraction (BQ.enqueue x q)` = `LQ.enqueue x (abstraction q)`.
While both sides still return the same results, we now have that the left side charges for zero cost (in `BQ.enqueue`), even though the right side claims to charge for one unit of cost (in `LQ.enqueue`).
To rectify this issue without changing the enqueue implementations, there's only one possible solution: make the `abstraction` function itself charge for some cost!

If the abstraction function were to incur cost, \\( \alpha(q)^\text{C} \\), the following condition would have to hold for the enqueue operation:
\\[ (\texttt{BQ.enqueue x q})^\text{C} + \alpha(\texttt{BQ.enqueue x q})^\text{C} = \alpha(\texttt{q})^\text{C} + (\texttt{LQ.enqueue x (abstraction q)})^\text{C} \\]
Letting \\( (\texttt{enqueue x c})^\text{AC} \coloneqq (\texttt{LQ.enqueue x (abstraction q)})^\text{C} \\), this is precisely the amortization conditions required on a potential function!
So, we can annotate the abstraction function itself with cost, according to the potential function:
```ocaml,hl_lines=3
let abstraction : BatchedQueue.t -> ListQueue.t =
  fun (inbox, outbox) ->
  charge (List.length inbox);
  outbox @ List.rev inbox
;;
```
This abstraction function integrates cost and behavior considerations, both charging according to the potential function and converting a `BatchedQueue.t` representation to a `ListQueue.t` representation.
The amortization conditions are exactly verified by the [abstraction function criteria](#abstraction-function).
Accordingly, the reasoning principles afforded by abstraction functions are upgraded to this cost-aware setting.
For example, as before, we can switch from using `BatchedQueue` to using `ListQueue` at any point in a sequence of operations and the results will cohere, including the cost (*i.e.*, the number of `$` symbols printed):
```ocaml,hl_lines=9-12
let demo =
  let module Q = BatchedQueue in
  let q = Q.empty () in
  let q = Q.enqueue 1 q in
  let q = Q.enqueue 2 q in
  let q = Q.enqueue 3 q in
  let n1, q = Q.dequeue q in
  let n2, q = Q.dequeue q in
  (* ⬆️ batched queue *)
  let module Q = ListQueue in
  let q = abstraction q in
  (* ⬇️ list queue *)
  let n3, _ = Q.dequeue q in
  print_newline ();
  n1, n2, n3
;;
```
We can again visualize this process as the composition of commutative squares:
<!-- https://q.uiver.app/#q=WzAsOCxbMywwLCJcXHRleHR0dHtpbnR9IFxcYXN0IFxcdGV4dHR0e0JRLnR9Il0sWzIsMCwiXFx0ZXh0dHR7QlEudH0iXSxbMywxLCJcXHRleHR0dHtpbnR9IFxcYXN0IFxcdGV4dHR0e0JRLnR9Il0sWzIsMSwiXFx0ZXh0dHR7TFEudH0iXSxbMCwwLCJcXHRleHR0dHt1bml0fSJdLFswLDEsIlxcdGV4dHR0e3VuaXR9Il0sWzEsMCwiXFx0ZXh0dHR7QlEudH0iXSxbMSwxLCJcXHRleHR0dHtMUS50fSJdLFswLDIsIlxcYWxwaGEnIl0sWzEsMCwiXFx0ZXh0dHR7ZGVxdWV1ZX0iXSxbMywyLCJcXHRleHR0dHtkZXF1ZXVlfSIsMl0sWzEsMywiXFxhbHBoYSJdLFs0LDUsIiIsMCx7InN0eWxlIjp7ImhlYWQiOnsibmFtZSI6Im5vbmUifX19XSxbNCw2LCJcXHRleHR0dHtlbXB0eX0iXSxbNSw3LCJcXHRleHR0dHtlbXB0eX0iLDJdLFs3LDMsIlxcdGV4dHR0e2VucXVldWUgeH0iLDJdLFs2LDEsIlxcdGV4dHR0e2VucXVldWUgeH0iXSxbNiw3LCJcXGFscGhhIl1d -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsOCxbMywwLCJcXHRleHR0dHtpbnR9IFxcYXN0IFxcdGV4dHR0e0JRLnR9Il0sWzIsMCwiXFx0ZXh0dHR7QlEudH0iXSxbMywxLCJcXHRleHR0dHtpbnR9IFxcYXN0IFxcdGV4dHR0e0JRLnR9Il0sWzIsMSwiXFx0ZXh0dHR7TFEudH0iXSxbMCwwLCJcXHRleHR0dHt1bml0fSJdLFswLDEsIlxcdGV4dHR0e3VuaXR9Il0sWzEsMCwiXFx0ZXh0dHR7QlEudH0iXSxbMSwxLCJcXHRleHR0dHtMUS50fSJdLFswLDIsIlxcYWxwaGEnIl0sWzEsMCwiXFx0ZXh0dHR7ZGVxdWV1ZX0iXSxbMywyLCJcXHRleHR0dHtkZXF1ZXVlfSIsMl0sWzEsMywiXFxhbHBoYSJdLFs0LDUsIiIsMCx7InN0eWxlIjp7ImhlYWQiOnsibmFtZSI6Im5vbmUifX19XSxbNCw2LCJcXHRleHR0dHtlbXB0eX0iXSxbNSw3LCJcXHRleHR0dHtlbXB0eX0iLDJdLFs3LDMsIlxcdGV4dHR0e2VucXVldWUgeH0iLDJdLFs2LDEsIlxcdGV4dHR0e2VucXVldWUgeH0iXSxbNiw3LCJcXGFscGhhIl1d&embed" width="647" height="304" style="border-radius: 8px; border: none;"></iframe>

The [telescoping sum of amortized analysis](#amortized-analysis) is hidden within this composition: rather than add a potential and immediately subtract it afterwards, the overlaying of adjacent uses of \\( \alpha \\) ensures that the intermediate potentials do not contribute to the global tally, computed by the outer edges of the larger rectangle built out of the individual squares.

# Conclusion {#conclusion}

In this post, we observed that a potential function used in amortized analysis is precisely the cost incurred by an abstraction function in a setting where cost is viewed as an effect.
In fact, viewed this way, nothing about the cost effect is special here: using this technique, we can amortize any effects.
For example, in [the paper](https://entics.episciences.org/14797), we observe that buffered string processing can be framed as amortization, where the potential function serves to flush the buffer.
While we considered the relatively simple example of batched queues here, the story generalizes to more complex scenarios, such as situations when the amortized cost described is an upper bound only on the true cost (in analogy with physics, data structures that sometimes experience "energy loss").
Beyond the inherent conceptual benefit of consolidation of ideas, viewing amortized analysis in this way also appears to be immensely practical: when verifying batched queues in [Calf](https://dl.acm.org/doi/abs/10.1145/3498670), the abstraction function perspective reduced the size of the verification from 700 lines of code down to 100 lines.
