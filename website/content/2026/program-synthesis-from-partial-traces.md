+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "Program Synthesis from Partial Traces"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2026-08-09

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Programming Languages", "Systems"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
# Consider these similar to keywords specified for a research paper.
tags = ["program synthesis", "automated reasoning"]

[extra]
author = {name = "Margarida Ferreira", url = "https://marghrid.github.io" }
# The committee specification is  a list of objects similar to the author.
committee = [
    {name = "Limin Jia", url = "https://www.andrew.cmu.edu/user/liminjia/"},
    {name = "Marijn Heule", url = "https://www.cs.cmu.edu/~mheule/"},
    {name = "Harrison Grodin", url = "https://www.harrisongrodin.com/"},

]

[markdown]
highlight_code = true

+++

Imagine you're a system administrator managing a complex cloud deployment. Day after day, you perform the same tedious sequence before leaving work: find, in the list of active computing instances, those no longer used by your team, select them, and click "Stop instances". Then, after a few seconds, you check whether they have already stopped; if not, you click "Force stop instances". Dozens of clicks through web interfaces like the one below, over and over again.

<span>
 <img
   style="display: block; margin: 1% auto;"
   src="./ec2-stop-instances.png"
   alt="EC2 interface to stop selected EC2 instances"
   width="350"
 />
</span>

What if, after a few days of silently watching you perform this task, the system could write the code to automate it for you, without you having to explain a single thing?

This is what the technique introduced in our paper [_Program Synthesis from Partial Traces_ (PLDI 2025)](https://arxiv.org/pdf/2504.14480) does!

> Our system, <span style="font-variant:small-caps;">Syren</span>, synthesizes general-purpose automation scripts from execution traces: the logs a system already records while its user performs a task by hand. Unlike prior approaches to program synthesis, which require users to actively describe what they want through formal specifications, input-output examples, or natural language, <span style="font-variant:small-caps;">Syren</span> works from data users already have. The challenge is that these traces are partial: they record the user's interactions with the system, but not the data transformations or control-flow decisions the user computes in their head. <span style="font-variant:small-caps;">Syren</span>'s key novelty is recovering these hidden computations: it starts from a trivial program that merely replays the traces, then applies program rewrites, backed by synthesis from input-output examples, to uncover the hidden logic and generalize the program into a readable script.


# Program Synthesis

For as long as we've had programming languages to automate our daily tasks, computer scientists have been thinking of ways to automate writing code itself.
That's the premise of _program synthesis_: the task of automatically generating executable code from a high-level specification. The journey began with logical formulations as specifications ([Manna & Waldinger, TOPLAS 1980](https://dl.acm.org/doi/10.1145/357084.357090)). These precise, mathematical specifications completely define the desired program's behavior, but they are expressed in a formal language that requires significant expertise to write.
Then came input-output examples, popularized by tools like Microsoft Excel's FlashFill ([Gulwani, POPL 2011](https://dl.acm.org/doi/10.1145/1926385.1926423)): "give me a program that for input X outputs Y."
Examples are much simpler, but in practice, they still require expertise and multiple iterations. They are inherently ambiguous because multiple programs can generate the same set of examples. This means the user has to cover specific corner cases and inspect the output for any unexpected behavior.
Recently, with advancements in large language models (LLMs), natural language emerged as the go-to specification ([Chen et al., 2021](https://doi.org/10.48550/arXiv.2107.03374)), making programming more accessible to non-experts than ever. But this comes at a cost: unlike logical formulas and examples, it's not clear how to verify that a program satisfies a natural-language specification.

All these synthesis specifications have something in common: they're _active_ specifications. They require users to explicitly articulate what they want, often through multiple rounds of clarification.
With <span style="font-variant:small-caps;">Syren</span>, we propose using _passive_ specifications instead: synthesizing programs from data users already have, requiring no additional knowledge or effort. Specifically, we synthesize programs from execution traces, the digital breadcrumbs left behind by every modern computing system to help us trace back its computations. These traces, whether sequences of API calls, network messages between servers, or system call logs, capture not just the everyday behaviors of systems but also corner cases and execution subtleties. They are already used for monitoring, debugging, and auditing, so why not use them to synthesize automations for hand-executed tasks in these systems, or optimized versions of existing routines?


# Synthesis from Partial Traces

The main challenge in synthesizing a program from real-world traces is that they provide only a partial view of what's happening. These traces record only some of the actions the user takes; for example, operations that get billed, or side-effecting executions that interact with external resources, such as network calls or file writes. They lack information about intermediate steps that may transform data internally or affect control flow.

Revisiting the example from the beginning: when the admin stops unused instances, every time they click a button in the visual console, the console calls a specific API method under the hood, and that call gets recorded. But the admin's decision to potentially force some computing instances to stop after a while, depending on each instance's status, is not recorded. This "computation" happens only in the user's head. To automate the task, we need to automate both sides of the computation: the visible API method calls and the _hidden_ computations that the user executes manually. Inferring these hidden functions poses a significant challenge for synthesis, but without them, the task can't be automated correctly.

For the purpose of this work, we define a _trace_ as the sequence of API methods invoked during a single execution of a task. The traces include the method name, inputs, and outputs for all API calls.
<span style="font-variant:small-caps;">Syren</span> synthesizes programs from these partial traces by inferring both control flow and non-trivial hidden functions without additional user input.


# <span style="font-variant:small-caps;">Syren</span>'s Synthesis Procedure {#synthesis-procedure}

<div style="max-width: 600px; margin: 1% auto;">
<svg viewBox="0 0 3249 1063" role="img" aria-label="Syren's synthesis procedure: input traces are turned into an initial program, which program rewriting turns into a final program. Click a stage to jump to it." style="display: block; width: 100%; height: auto;">
<style>
.syren-hotspot { fill: #c8102e; fill-opacity: 0; stroke: #c8102e; stroke-opacity: 0; stroke-width: 14; transition: fill-opacity .15s, stroke-opacity .15s; }
svg a:hover .syren-hotspot, svg a:focus .syren-hotspot { fill-opacity: .05; stroke-opacity: .75; }
</style>
<image href="./syrens-system.png" x="0" y="0" width="3249" height="1063" />
<a href="#example-execution"><title>Input traces: jump to the example traces</title><rect class="syren-hotspot" x="0" y="170" width="670" height="830" rx="30" /></a>
<a href="#initial-program"><title>Initial program: jump to how the initial program is built</title><rect class="syren-hotspot" x="950" y="40" width="590" height="960" rx="30" /></a>
<a href="#rewriting-the-original-program"><title>Program rewriting: jump to the rewrite steps</title><rect class="syren-hotspot" x="1820" y="200" width="510" height="835" rx="30" /></a>
<a href="#final-program"><title>Final program: jump to the synthesized script</title><rect class="syren-hotspot" x="2650" y="250" width="590" height="750" rx="30" /></a>
</svg>
<p style="text-align: center; font-size: 85%; font-style: italic; margin: 0.3em 0 0;">Click a stage of the diagram to jump to its explanation.</p>
</div>
<span style="font-variant:small-caps;">Syren</span>'s synthesis starts by ingesting input traces, the sequences of actions recorded when someone is executing a task. These traces are turned into an initial version of the automation program that simply replays each trace exactly as observed. It is correct by construction, but way too rigid for real-world use. So <span style="font-variant:small-caps;">Syren</span> then moves into program rewriting, using a library of rules to generalize the code and uncover the "hidden logic" that isn't logged. In the end, <span style="font-variant:small-caps;">Syren</span> outputs a high-level, human-readable script that can automate the task in the scenarios observed in the traces, but also across new ones.


## Example Execution {#example-execution}


Performing the example cloud computing task described above in the Amazon Web Services (AWS) console produces logs that show the sequence of underlying API calls made by the system. These logs can be input as traces into <span style="font-variant:small-caps;">Syren</span> for synthesis. Below is an example trace of the execution of this task for a single computing instance with ID `"i-12345"`, which we call Trace #1:


```syren
(
 ec2.StopInstances("InstanceIds": ["i-12345"], "force": false),
 { ... }
)


(
 ec2.DescribeInstanceStatus("InstanceIds": ["i-12345"]),
 {"InstanceState": "stopped", ...}
)
```


Trace #1 contains two API calls, `ec2.StopInstances` and `ec2.DescribeInstanceStatus`, each represented as a pair in parentheses: the first element of the pair shows the API method name and its inputs (the request parameters), and the second shows its output (the response). In the output of `ec2.DescribeInstanceStatus`, the instance is showing as `"stopped"`. That is the goal; the system admin's task is complete.


The next day, the system admin could execute the same task on instance `"i-54321"` and generate the following trace (Trace #2):


```syren
(
 ec2.StopInstances("InstanceIds": ["i-54321"], "force": false),
 { ... }
)


(
 ec2.DescribeInstanceStatus("InstanceIds":["i-54321"]),
 {"InstanceState": "stopping", ...}
)


(
 ec2.StopInstances("InstanceIds": ["i-54321"], "force": true),
 { ... }
)
```


In this second execution of the task, `ec2.DescribeInstanceStatus` shows the current status of the instance as `"stopping"` (not `"stopped"`), so there is a second call to `ec2.StopInstances` with `force` set to `true`.


When working with traces like these, there's always a trivial solution: a program that exactly reproduces the input traces. But users don't want this brittle reproduction; they want a program that _generalizes_ beyond the examples they've shown. Our cloud administrator doesn't need a script that stops the exact computing instances they've stopped in the past; they need one that takes a list of instance IDs as a parameter, handling the repetitive parts automatically while still letting them provide the essential information.
This trivial program is still useful to <span style="font-variant:small-caps;">Syren</span>: it serves as the starting point of our synthesis, which progressively makes it more general and readable.


### Initial Program {#initial-program}

<span style="font-variant:small-caps;">Syren</span>'s programs are written in a programming language formally defined in [the paper](https://arxiv.org/pdf/2504.14480). Its syntax and semantics are similar to those of commonly used imperative languages, such as Python, so users with programming backgrounds can read and edit <span style="font-variant:small-caps;">Syren</span> programs, and these programs can be easily compiled to other languages.


We build the initial program by branching the execution on the value of a fresh integer variable, `br`, which is received as an input parameter, and replaying each trace on a different branch. In <span style="font-variant:small-caps;">Syren</span>'s syntax, we explicitly represent the program's input parameters on the first line, preceded by a `λ`. So, `λ br.` in the first line means the program takes as input one parameter, `br`. In the initial program, the sequence of API calls is reproduced exactly as shown in the traces, and all values are hard-coded constants.
For the two traces shown before, <span style="font-variant:small-caps;">Syren</span>'s initial program would be:

```syren
λ br.
if br == 1 {
  let x_1_1 = ec2.StopInstances(instanceIds=["i-12345"], force=false)
  let x_1_2 = ec2.DescribeInstanceStatus(instanceIds=["i-12345"])
} else {
  let x_2_1 = ec2.StopInstances(instanceIds=["i-54321"], force=false)
  let x_2_2 = ec2.DescribeInstanceStatus(instanceIds=["i-54321"])
  let x_2_3 = ec2.StopInstances(instanceIds=["i-54321"], force=true)
}
```


This program will reproduce Trace #1 if the parameter `br` is set to `1` and Trace #2 otherwise. In practice, <span style="font-variant:small-caps;">Syren</span> uses more than two traces, so there are more conditionals in this top-level if-else chain.


This initial program is correct by construction: for each trace the user provided, there exists an input for which the program reproduces it. But it doesn't generalize beyond the traces, so, from here, <span style="font-variant:small-caps;">Syren</span> applies a series of _optimizing rewrites_: compiler-like, correctness-preserving transformations that make the program more general, more readable, and thus closer to the ideal program we want to return to the user.

### Rewriting the Original Program {#rewriting-the-original-program}


<span style="font-variant:small-caps;">Syren</span>'s first rewrites replace the instance IDs, which are constants hard-coded repeatedly in multiple calls, with a new input parameter to the script, `i_0`. They also pull the first call to `ec2.StopInstances` and the call to `ec2.DescribeInstanceStatus` out of the if-statement, since they are identical in both branches. These rewrites reduce the program size and eliminate repeated API calls, two of <span style="font-variant:small-caps;">Syren</span>'s optimization goals. The program below is the result of these transformations.

<div class="code-before" data-hl='["i-12345"] ;; ["i-54321"]' data-arrows='3-4>2 ;; 6-7>2'>

```syren,hl_lines=3-4 6-8
λ br.
if br == 1 {
  let x_1_1 = ec2.StopInstances(instanceIds=["i-12345"], force=false)
  let x_1_2 = ec2.DescribeInstanceStatus(instanceIds=["i-12345"])
} else {
  let x_2_1 = ec2.StopInstances(instanceIds=["i-54321"], force=false)
  let x_2_2 = ec2.DescribeInstanceStatus(instanceIds=["i-54321"])
  let x_2_3 = ec2.StopInstances(instanceIds=["i-54321"], force=true)
}
```

</div>

<span>
  <img
    style="display: block; margin: 1em auto 0;"
    src="./arrow.png"
    alt="An arrow pointing down"
    width="35"
  />
</span>

<div class="code-after" data-hl='i_0'>

```syren,hl_lines=1-3 5
λ br, i_0.
let x_1 = ec2.StopInstances(instanceIds=i_0, force=false)
let x_2 = ec2.DescribeInstanceStatus(instanceIds=i_0)
if !(br == 1) {
  let x_2_3 = ec2.StopInstances(instanceIds=i_0, force=true)
}
```

</div>

The program above still depends on `br`, an artificial variable with no real semantic meaning: the conditional `!(br==1)` decides whether the second, forced call to `ec2.StopInstances` runs. <span style="font-variant:small-caps;">Syren</span> could remove it as it did the instance IDs, by introducing a new input parameter, in this case a Boolean that the user would set to request the forced stop. But that is not what happened in the example task: the administrator decided whether to force the stop based on the outcome of the previous call to `ec2.DescribeInstanceStatus`. If the instance does not show as `"stopped"` yet, they force it.

<span style="font-variant:small-caps;">Syren</span> always tries to infer these hidden data dependencies on previous instructions in the script before defaulting to introducing new parameters. So, in the final rewrite of this example, it replaces `!(br==1)` with the output of a new function `φ`, a stand-in for the computation the user performed in their head. Since we don't know what previous information the user relied on, `φ` takes as input all variables in scope at this point in the program. `φ` remains undefined for now, so we declare the program is parametric on its implementation in the first line with `Λ φ.`.

<div class="code-before" data-hl='λ br|br ;; !(br == 1)'>

```syren,hl_lines=1 4
λ br, i_0.
let x_1 = ec2.StopInstances(instanceIds=i_0, force=false)
let x_2 = ec2.DescribeInstanceStatus(instanceIds=i_0)
if !(br == 1) {
  let x_2_3 = ec2.StopInstances(instanceIds=i_0, force=true)
}
```

</div>

<span>
  <img
    style="display: block; margin: 1em auto 0;"
    src="./arrow.png"
    alt="An arrow pointing down"
    width="35"
  />
</span>

<div class="code-after" data-hl='Λ φ.|φ. ;; c = φ(i_0, x_1, x_2) ;; if c {|c'>

```syren,hl_lines=1 4-5
Λ φ. λ i_0.
let x_1 = ec2.StopInstances(instanceIds=i_0, force=false)
let x_2 = ec2.DescribeInstanceStatus(instanceIds=i_0)
let c = φ(i_0, x_1, x_2)
if c {
  let x_2_3 = ec2.StopInstances(instanceIds=i_0, force=true)
}
```

</div>


### Example-Based Synthesis of Hidden Functions

Of course, this program is only useful if we can provide an implementation `f` for `φ` for which the program can perform the task. This is where example-based synthesis comes in.
During the rewrite process, we maintain a mapping from program identifiers to their corresponding values in the traces. Then, we use these mappings to compute a set of input-output constraints that `f` must satisfy, and feed them to an off-the-shelf example-based synthesizer to generate an implementation of `φ`. <span style="font-variant:small-caps;">Syren</span> supports two such synthesizers: [Rosette](https://emina.github.io/rosette/index.html) ([Torlak et al., Onward! 2013](https://dl.acm.org/doi/10.1145/2509578.2509586)) and [cvc5](https://cvc5.github.io/) ([Barbosa et al., TACAS 2022](https://doi.org/10.1007/978-3-030-99524-9_24)).

Looking side by side at the program above and the traces it was built from, we can read off the values `φ`'s arguments take in each trace: `i_0` is the instance ID, and `x_1` and `x_2` are the responses of the two API calls, as annotated in the constraints below. The output of `φ` is a Boolean value that indicates whether the instance has not yet stopped and needs to be forced to stop: `false` for the first trace and `true` for the second.

So, for the traces and program in this example, we know `f` must be such that:

```syren
f(["i-12345"], /* parameter i_0 */
  {"StoppingInstances": [...], "ResponseMetadata": {...}}, /* response from StopInstances, x_1 */
  {"InstanceState" : "stopped", ...} /* response from DescribeInstanceStatus, x_2 */
) = false
```

for Trace #1, and

```syren
f(["i-54321"], /* parameter i_0 */
  {"StoppingInstances": [...], "ResponseMetadata": {...}}, /* response from StopInstances, x_1 */
  {"InstanceState" : "stopping", ...} /* response from DescribeInstanceStatus, x_2 */
) = true
```

for Trace #2.

From these constraints, the synthesizer generates the simplest logical expression that fits the behavior in the traces, giving the following implementation `f` for `φ`:

```syren
f := (i_0, x_1, x_2) -> x_2.InstanceState != "stopped"
```

Substituting `f` for `φ` yields a program that is correct by construction. Since `f` uses only its last input, we simplify it to take just `x_2`.



<div class="code-before" id="final-program" data-hl='Λ φ.|φ. ;; c = φ(i_0, x_1, x_2) ;; if c {|c'>

```syren,hl_lines=1 4-5
Λ φ. λ i_0.
let x_1 = ec2.StopInstances(instanceIds=i_0, force=false)
let x_2 = ec2.DescribeInstanceStatus(instanceIds=i_0)
let c = φ(i_0, x_1, x_2)
if c {
  let x_2_3 = ec2.StopInstances(instanceIds=i_0, force=true)
}
```

</div>

<span>
  <img
    style="display: block; margin: 1em auto 0;"
    src="./arrow.png"
    alt="An arrow pointing down"
    width="35"
  />
</span>

<div class="code-after" data-hl='c = f(x_2) ;; if c {|c ;; f := (x) -> x.InstanceState != "stopped"'>

```syren,hl_lines=4-5 9
λ i_0.
let _ = ec2.StopInstances(instanceIds=i_0, force=false)
let x_2 = ec2.DescribeInstanceStatus(instanceIds=i_0)
let c = f(x_2)
if c {
  let _ = ec2.StopInstances(instanceIds=i_0, force=true)
}
where
f := (x) -> x.InstanceState != "stopped"
```

</div>

This final program executes the task described at the beginning!

## Beyond the Example: Search over a Library of Rewrites

<span style="font-variant:small-caps;">Syren</span>'s library of rewrite rules includes many more rules than the ones used in the example above.
Rewrites fall into two categories:


> __Refinement rules__ are simple structural transformations. These might lift identical statements out of conditionals or replace constants with parameters. They are correctness-preserving by construction and don't require synthesis. They uncover the program's control flow in a way that explains the observed traces.


> __Synthesis rules__ introduce hidden functions. They replace expressions with fresh calls to unknown functions \\(\varphi\\), which are later synthesized from input-output examples. These rules apply only if a valid implementation of \\(\varphi\\) that preserves trace behavior exists.


All rewrite rules are defined as patterns. As an example, below is the definition of the first rewrite rule shown in the example above, which extracts an identical sequence of instructions \\(\mathcal{R}\\) from both the then-branch and the else-branch of a conditional. \\(\mathcal{R}\\), \\(\mathcal{S}\\), \\(\mathcal{T}\\), \\(\mathcal{U}\\), and \\(\mathcal{V}\\) are arbitrary sequences of instructions in the program.

<span>
  <img
    style="display: block; margin: 1% auto;"
    src="./rewrite.png"
    alt="Figure showing a rewrite rule: a pattern with abstract constructs on the left, and the resulting pattern on the right."
    width="220"
  />
</span>

When the program <span style="font-variant:small-caps;">Syren</span> is considering has the structure on the left, the rule applies, and the program is rewritten with the structure on the right. The application of synthesis rules is subject to an additional constraint: synthesizing any required hidden functions. When we can't find an implementation for \\(\varphi\\), whether it is used in a control-flow conditional or as an input to a function call, that indicates the rewrite is misguided.


At any stage of the rewrite process, many rules can be applied to the program, too many to try them all. Instead, <span style="font-variant:small-caps;">Syren</span> performs a cost-directed search, using a cost function that penalizes undesirable program characteristics.
The cost functions in <span style="font-variant:small-caps;">Syren</span> prefer smaller, more general, and human-readable programs.
In the paper, we implement two concrete cost functions that illustrate how different notions of "simplicity" yield different outcomes.


The first, \\(\chi_{\mathrm{syn}}\\), follows the widely used [Occam's razor principle](https://en.wikipedia.org/wiki/Occam%27s_razor) and favors purely syntactic simplicity: it assigns a weighted penalty to every statement, every parameter, and every use of the synthetic variable `br`.
\\(\chi_{\mathrm{syn}}\\) produces a fine-grained score that distinguishes most programs from one another, giving the search a clear signal at nearly every step.


<span style="font-variant:small-caps;">Syren</span> implements a second cost function, \\(\chi_{\mathrm{T}}\\), which takes a more semantic view of the programs: rather than counting syntactic elements, it measures how much each API call is reused across the input traces. A statement executed many times, such as an API call inside a loop shared across traces, contributes more reuse and therefore incurs lower \\(\chi_{\mathrm{T}}\\) cost than the same calls written out redundantly in separate branches. It also penalizes branches that only reproduce a single input trace, treating them as corner cases that suggest the program has not yet generalized. In practice, \\(\chi_{\mathrm{T}}\\) is worse at directing the search than \\(\chi_{\mathrm{syn}}\\), because it is coarser: more programs have the same score. With either cost function, <span style="font-variant:small-caps;">Syren</span> synthesizes programs for a similar number of tasks, but \\(\chi_{\mathrm{syn}}\\) generates programs that are easier to read.


The cost function does more than rank programs after applying rewrites. It actively controls which rewrites to apply at every step of the search. <span style="font-variant:small-caps;">Syren</span> treats the two types of rewrites differently. At each step, it first scans all applicable refinement rules and greedily applies the one that yields the greatest cost reduction, repeating this until no refinement rule can lower the cost further. Only then does it consider synthesis rules, again selecting the most cost-reducing one and invoking the example-based solver to check whether a valid implementation exists for any newly introduced computation. This ordering exhausts the cheap structural rewrites first, so the solver is called as sparingly as possible.
As with the cost function itself, <span style="font-variant:small-caps;">Syren</span>'s source code provides predefined search strategies but allows users to define their own.


# Final Thoughts


<span style="font-variant:small-caps;">Syren</span> is, to our knowledge, the first approach to synthesizing programs that combine side-effecting API calls, control flow, and hidden pure functions purely from execution traces: no annotations, no natural language, no hand-crafted examples.

In [the paper](https://arxiv.org/pdf/2504.14480), we showcase <span style="font-variant:small-caps;">Syren</span>'s practical applicability. We evaluate it on 54 real-world tasks, including cloud automation, filesystem manipulation, and document editing scripts, drawn from custom tasks, existing [AWS Automation Runbooks](https://docs.aws.amazon.com/systems-manager-automation-runbooks/latest/userguide/automation-runbook-reference.html), [Blink Automations](https://www.blinkops.com/), and [related work from Guo et al. at PLDI 2022](https://dl.acm.org/doi/10.1145/3519939.3523450). The underlying example-based synthesizer generates non-trivial data transformations that allow <span style="font-variant:small-caps;">Syren</span> to uncover more intricate computations that are not visible in the traces. <span style="font-variant:small-caps;">Syren</span> introduces control structures like if-then-else conditionals and retry-until loops, and synthesizes correct, human-meaningful scripts for 39 of the 54 tasks in under 5 minutes.

Though powerful, the synthesis of data transformations is <span style="font-variant:small-caps;">Syren</span>'s main bottleneck: when the hidden functions require complex manipulation of JSON data, the underlying example-based synthesizer can fail to find the right expression, either due to the time limit imposed or because the required computation is not in the language of JSON operations we use. Improving <span style="font-variant:small-caps;">Syren</span>'s performance would require more specialized grammars or solvers for this domain.
There is another limitation worth acknowledging beyond performance: the quality of <span style="font-variant:small-caps;">Syren</span>'s programs depends heavily on having sufficiently rich and diverse traces. If the traces don't capture the data needed to compute a value, <span style="font-variant:small-caps;">Syren</span> falls back to treating that value as an input parameter. Two very similar traces may provide too little signal for the synthesis-by-example solver to distinguish the right hidden function from a degenerate one.
Looking ahead, there are natural extensions to explore. Real-world traces are recorded from humans, and humans are inconsistent. An action a user took once in an unusual mood may not reflect the general pattern they want to automate, but <span style="font-variant:small-caps;">Syren</span> currently tries to explain every trace it's given, treating all of them as equally intentional. A natural extension would be allowing <span style="font-variant:small-caps;">Syren</span> to identify and discard outlier traces, synthesizing a program that fits the majority of the observed behavior rather than demanding a perfect explanation for all of it.

As systems become more API-driven and observability tooling improves, the resulting raw logs become more abundant. <span style="font-variant:small-caps;">Syren</span> takes a step towards a future where that data doesn't just sit in a dashboard waiting to be analyzed, but actively gets turned into automation. Instead of asking users to articulate what they want, we can just watch what they do.


<style>
pre > code {
  font-size: 100%;
}

pre , code {
  font-size: 77%;
}

/* Changed-code highlights.
   The hl_lines marks highlight whole lines and serve as the no-JS fallback;
   the script at the end of this page replaces them with character-precise
   highlights (the ::highlight rules) in browsers that support the
   CSS Custom Highlight API. .code-before = about to change (red),
   .code-after = changed/new (green). */
pre mark {
  display: block;
  color: inherit;
}
.code-before pre mark {
  background-color: rgba(217, 115, 115, 0.25) !important;
}
.code-after pre mark {
  background-color: rgba(102, 255, 166, 0.15) !important;
}
::highlight(syren-before-chars) {
  background-color: rgba(217, 115, 115, 0.4);
}
::highlight(syren-after-chars) {
  background-color: rgba(102, 255, 166, 0.3);
}

/* Code highlight options: */
/* pre {
  padding: 1rem;
  overflow: auto;
} */
/* The line numbers already provide some kind of left/right padding */
/* pre[data-linenos] {
  padding: 1rem 0;
}
pre table td {
  padding: 0;
} */
/* The line number cells */
/* pre table td:nth-of-type(1) {
  text-align: center;
  vertical-align: top;
  user-select: none;
} */
pre mark {
  /* If you want your highlights to take the full width */
  /* display: block; */
  /* The default background colour of a mark is bright yellow */
  /* background-color: rgba(254, 252, 232, 0.9); */
  /* background-color: rgba(230, 222, 212, .5); */

}
/* pre table {
  width: 100%;
  border-collapse: collapse;
} */

main .about table, main .post table  {
box-shadow: none;
}


</style>

<script>
// Character-precise highlights for the changed code.
// Each .code-before/.code-after block lists its changed snippets in
// a data-hl attribute: entries are separated by ";;". A plain entry
// highlights every occurrence of that text; an entry "search|inner"
// highlights only "inner" inside the first occurrence of "search".
// Requires the CSS Custom Highlight API; without it (or with JS disabled)
// the whole-line hl_lines marks remain as a fallback.
(() => {
  if (typeof Highlight !== "function" || !("highlights" in CSS)) return;
  const names = { "code-before": "syren-before-chars", "code-after": "syren-after-chars" };
  for (const cls in names) {
    const ranges = [];
    for (const div of document.querySelectorAll("div." + cls + "[data-hl]")) {
      const code = div.querySelector("pre code");
      if (!code) continue;
      // Drop the whole-line fallback marks; text and selection are unaffected.
      for (const m of code.querySelectorAll("mark")) m.replaceWith(...m.childNodes);
      code.normalize();
      const nodes = [];
      const walker = document.createTreeWalker(code, NodeFilter.SHOW_TEXT);
      for (let n = walker.nextNode(), start = 0; n; n = walker.nextNode()) {
        nodes.push({ n, start });
        start += n.data.length;
      }
      const locate = pos => {
        for (let i = nodes.length - 1; i >= 0; i--)
          if (nodes[i].start <= pos) return [nodes[i].n, pos - nodes[i].start];
      };
      const text = code.textContent;
      for (const entry of div.dataset.hl.split(";;")) {
        const [search, inner] = entry.split("|").map(s => s.trim());
        for (let from = 0; ; ) {
          const at = text.indexOf(search, from);
          if (at === -1) break;
          const s = inner ? at + search.indexOf(inner) : at;
          const e = inner ? s + inner.length : at + search.length;
          const r = new Range();
          r.setStart(...locate(s));
          r.setEnd(...locate(e));
          ranges.push(r);
          if (inner) break;
          from = at + search.length;
        }
      }
    }
    CSS.highlights.set(names[cls], new Highlight(...ranges));
  }
})();
// Curved "moved out" arrows on code blocks. A data-arrows attribute lists
// ";;"-separated entries "from>to": a curved arrow is drawn in a left gutter
// from beside line `from` (fractions land between lines) up to the left of
// line `to`'s top edge. Redrawn on resize and after fonts load.
(() => {
  const divs = [...document.querySelectorAll("div[data-arrows]")];
  if (!divs.length) return;
  const NS = "http://www.w3.org/2000/svg";
  const draw = () => {
    for (const div of divs) {
      const pre = div.querySelector("pre"), code = div.querySelector("pre code");
      if (!pre || !code) continue;
      div.querySelector(".syren-move-arrows")?.remove();
      const em = parseFloat(getComputedStyle(code).fontSize);
      pre.style.position = "relative";
      pre.style.paddingLeft = (3.4 * em) + "px";
      const preR = pre.getBoundingClientRect(), codeR = code.getBoundingClientRect();
      const lineCount = code.textContent.replace(/\n$/, "").split("\n").length;
      const lineH = codeR.height / lineCount;
      const top0 = codeR.top - preR.top;
      const svg = document.createElementNS(NS, "svg");
      svg.setAttribute("class", "syren-move-arrows");
      svg.setAttribute("aria-hidden", "true");
      svg.style.cssText = "position:absolute;left:0;top:0;width:100%;height:100%;pointer-events:none;overflow:visible;";
      const color = div.classList.contains("code-after") ? "rgba(102, 255, 166, 0.5)" : "rgba(217, 115, 115, 0.6)";
      div.dataset.arrows.split(";;").map(s => s.trim()).forEach((entry, i) => {
        const [fromSpec, toSpec] = entry.split(">");
        const span = fromSpec.split("-").map(Number);
        const to = Number(toSpec);
        let sy;
        if (span.length === 2) {
          // A line range: draw a bracket spanning those lines, arrow from its middle.
          const yTop = top0 + (span[0] - 1) * lineH + 2, yBot = top0 + span[1] * lineH - 2;
          sy = (yTop + yBot) / 2;
          const bx = 4.0 * em, tick = 0.3 * em;
          const bracket = document.createElementNS(NS, "path");
          bracket.setAttribute("d", `M ${bx + tick} ${yTop} L ${bx} ${yTop} L ${bx} ${yBot} L ${bx + tick} ${yBot}`);
          bracket.setAttribute("fill", "none");
          bracket.setAttribute("stroke", color);
          bracket.setAttribute("stroke-width", "2.5");
          svg.appendChild(bracket);
        } else {
          sy = top0 + (span[0] - 0.5) * lineH;
        }
        const sx = 3.95 * em;
        const tx = (3.3 - i * 0.8) * em, ty = top0 + (to - 1) * lineH;
        const cx = Math.max(0.4 * em, tx - 0.9 * em);
        const p = document.createElementNS(NS, "path");
        p.setAttribute("d", `M ${sx} ${sy} C ${cx} ${sy}, ${cx} ${ty + lineH * 0.2}, ${tx} ${ty}`);
        p.setAttribute("fill", "none");
        p.setAttribute("stroke", color);
        p.setAttribute("stroke-width", "2.5");
        svg.appendChild(p);
        const ang = Math.atan2(-lineH * 0.2, tx - cx), h = 0.6 * em;
        // Head tip sits slightly forward of the curve end, along its direction.
        const hx = tx + 0.35 * em * Math.cos(ang), hy = ty + 0.35 * em * Math.sin(ang);
        const head = document.createElementNS(NS, "path");
        head.setAttribute("d", `M ${hx} ${hy} L ${hx + h * Math.cos(ang + 2.6)} ${hy + h * Math.sin(ang + 2.6)} L ${hx + h * Math.cos(ang - 2.6)} ${hy + h * Math.sin(ang - 2.6)} Z`);
        head.setAttribute("fill", color);
        svg.appendChild(head);
      });
      pre.appendChild(svg);
    }
  };
  draw();
  document.fonts?.ready?.then(draw);
  addEventListener("resize", () => { clearTimeout(draw._t); draw._t = setTimeout(draw, 150); });
})();
</script>
