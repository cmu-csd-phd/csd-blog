+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "Program Synthesis from Partial Traces"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2026-08-01

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
    {name = "Harry Q. Bovik", url = "http://www.cs.cmu.edu/~bovik/"},
    {name = "Committee Member 2's Full Name", url = "Committee Member 2's page"},
    {name = "Committee Member 3's Full Name", url = "Committee Member 3's page"}
]

[markdown]
highlight_code = true
highlight_theme = "ayu-light"

+++

Imagine you're a system administrator managing a complex cloud deployment. Day after day, you perform the same tedious sequence before leaving work: find in a list of active computing instances those that are no longer being used by your team, select them, and click "Stop Instances". Then, after a few seconds, you check whether they have already stopped; if not, you click "Force stop instances". Dozens of clicks through web interfaces like the one below, over and over again.

<span>
 <img
   style="display: block; margin: auto;"
   src="./ec2-stop-instances.png"
   alt="EC2 interface to stop selected EC2 instances"
   width="350em"
   style="margin: 1%"
 />
</span>

What if, after a few days of silently recording you perform this task every day, the system could write the code to automate it for you, without you having to explain a single thing?

This is what the technique introduced in our paper [_Program Synthesis from Partial Traces_ (PLDI 2025)](https://arxiv.org/pdf/2504.14480) does! This post walks through the main ideas behind our system, <span style="font-variant:small-caps;">Syren</span>, which synthesizes general-purpose scripts from logs that only partially capture the desired program behavior.


# Program Synthesis

For as long as we've had programming languages to automate our daily tasks, computer scientists have been thinking of ways to automate writing code itself.
That's the premise of _program synthesis_: the task of automatically generating executable code from a high-level specification. The journey began with logical formulations as specifications ([Manna & Waldinger, TOPLAS 1980](https://dl.acm.org/doi/10.1145/357084.357090)). These precise, mathematical specifications completely define the desired program's behavior, but require significant expertise. Then came input-output examples, popularized by tools like Microsoft Excel's FlashFill ([Gulwani, POPL 2011](https://dl.acm.org/doi/10.1145/1926385.1926423)): "give me a program that for input X outputs Y." These are much simpler but still demand specific knowledge and are inherently ambiguous, usually requiring multiple iterations to get right. Recently, with advancements in large language models (LLMs), natural language emerged as the go-to specification ([Chen et al., 2021](https://doi.org/10.48550/arXiv.2107.03374)), making programming more accessible to non-experts than ever. But this comes at a cost: unlike logical formulas and examples, it's not clear how to verify that a program satisfies a natural-language specification.

All these synthesis specifications have something in common: they're _active_ specifications. They require users to explicitly articulate what they want, often through multiple rounds of clarification.
With <span style="font-variant:small-caps;">Syren</span>, we propose using _passive_ specifications instead: synthesize programs from data users already have, requiring no additional knowledge or effort. We propose program synthesis from execution traces, which serve as digital breadcrumbs left behind by every modern computing system to help us trace back their computations. These traces, whether sequences of API calls, network messages between servers, or system call logs, capture not just the everyday behaviors of systems but also corner cases and implementation subtleties. They are used for monitoring, debugging, and auditing, so why not use them to synthesize programs?


# Synthesis from Partial Traces

The main challenge to consider when synthesizing a program from real-world traces is that they provide only a partial view of what's happening. These traces record only some of the actions the user takes; for example, operations that get billed, or side-effecting executions that interact with external resources, such as network calls or file writes. They lack information about intermediate steps that may transform data internally or affect control flow.

Revisiting the example from the beginning: when the admin stops unused instances, every time they click a button in the visual console, it calls under the hood a specific API method, and that gets recorded. But their decision to potentially force some computing instances to stop after a while, based on their status, does not get recorded. This "computation" happens only in the user's head. To automate the task, we need to automate both sides of the computation: the visible API method calls and the _hidden_ computations that the user executes manually. Inferring these hidden functions poses a significant synthesis challenge, but without them, the task can't be automated correctly.

For the purpose of this work, we define a _trace_ as the sequence of API methods invoked during a single execution of a task. The traces include the method name, inputs, and outputs for all API calls.
<span style="font-variant:small-caps;">Syren</span> synthesizes programs from these partial traces by inferring both control flow and non-trivial hidden functions without additional user input. We combine program rewrites of a trivial solution to introduce control flow with synthesis from input-output examples to discover the hidden functions between data in the traces.


# <span style="font-variant:small-caps;">Syren</span>'s Synthesis Procedure

<span>
  <img 
    style="display: block; margin: auto;" 
    src="./syrens-system.png"
    alt="Syren's synthesis procedure."
    width="600em"
    style="margin: 1%"
  />
</span>

<span style="font-variant:small-caps;">Syren</span>'s synthesis starts by ingesting input traces, the sequences of actions recorded when someone is executing a task. These traces are turned into an initial version of the automation program that simply replays each trace exactly as observed. This program is correct by construction, in the sense that it can reproduce all the traces taken as input, but way too rigid for real-world use. So <span style="font-variant:small-caps;">Syren</span> then moves into program rewriting, using a library of rules to generalize the code and uncover the "hidden logic" that isn't logged. In the end, <span style="font-variant:small-caps;">Syren</span> outputs a high-level, human-readable script that can automate the task in the scenarios observed in the traces, but also across new ones.


## Example Execution


Performing the example cloud computing task described above in the Amazon Web Services (AWS) console produces logs that show the sequence of underlying API calls made by the system. These logs can be input as traces into <span style="font-variant:small-caps;">Syren</span> for synthesis. Below, we show an example of a trace showing the execution of this task for a single computing instance, with ID `"i-12345"`, Trace #1:


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


Each trace contains the name of the API call, its request parameters (i.e., inputs), and its response parameters (outputs). In Trace #1, there are two API calls, represented as pairs in parentheses: `ec2.StopInstances` and `ec2.DescribeInstanceStatus`. The first element of the pair shows the API method name and its inputs, and the second shows the response to that API call, i.e., its output. We see that in the output of `ec2.DescribeInstanceStatus`, the instance is showing as `"stopped"`. That is the goal, so in this case, the system admin's task is concluded.


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


In this second execution in the task, `ec2.DescribeInstanceStatus` does _not_ show the current status of the instance as `"stopped"`, so there is a second call to `ec2.StopInstances` with `force` set to `true`.


When working with traces like these, there's always a trivial solution: a program that exactly reproduces the input traces. But users don't want this brittle reproduction; they want a program that _generalizes_ beyond the examples they've shown. Our cloud administrator doesn't need a script that stops the exact compute instances they've stopped in the past; they need one that takes a list of instance IDs as a parameter, handling the repetitive parts automatically while still letting them provide the essential information.
Even though this trivial program that reproduces all the traces exactly is not what the user is looking for, it's useful for <span style="font-variant:small-caps;">Syren</span>. We use it as a starting point for our synthesis, and progressively improve it by making it more general and readable.


### Initial program:

<span style="font-variant:small-caps;">Syren</span>'s programs are written in a programming language formally defined in [the paper](https://arxiv.org/pdf/2504.14480). It's similar to other scripting languages, such as Python, so users with programming backgrounds can read and edit programs. Its syntax and semantics match those of other commonly used imperative languages, so <span style="font-variant:small-caps;">Syren</span> programs can be easily compiled to other languages.


We build the initial program by branching the execution on the value of a fresh integer variable, `br`, which is received as an input parameter, and replaying each trace on a different branch. In <span style="font-variant:small-caps;">Syren</span>'s syntax, we explicitly represent the program's input parameters on the first line, preceded by a `λ`. So, `λ br.` in the first line means the program takes as input one parameter, `br`. In the initial program, the sequence of API calls is reproduced exactly as shown in the traces, and all values are hard-coded constants.
For the two traces shown before, <span style="font-variant:small-caps;">Syren</span>'s initial program would be:

<span>
  <img 
    style="display: block; margin: auto; background-color: #fffbf0;" 
    width="554em"
    src="./code_snippet_00.png"
    alt="A code snippet containing with the following source code:
    λ br.
    if br == 1 {
      let x_1_1 = ec2.StopInstances(instanceIds=['i-12345'], force=false)
      let x_1_2 = ec2.DescribeInstanceStatus(instanceIds=['i-12345'])
    } else {
      let x_2_1 = ec2.StopInstances(instanceIds=['i-54321'], force=false)
      let x_2_2 = ec2.DescribeInstanceStatus(instanceIds=['i-54321'])
      let x_2_3 = ec2.StopInstances(instanceIds=['i-54321'], force=true)
    }
    "
  />
</span>


This program will reproduce Trace #1 if the parameter `br` is set to `1` and Trace #2 otherwise. In practice, <span style="font-variant:small-caps;">Syren</span> uses more than two traces, so there are more conditionals in this top-level if-else chain.


This initial program is correct by construction: there exists an input for which it reproduces all the traces the user provided. But it's likely not something that the user can use to automate their task, since it doesn't generalize beyond the traces. So, from here, <span style="font-variant:small-caps;">Syren</span> applies a series of _optimizing rewrites_, compiler-like program rewrites that improve the program, making it more general, readable, and thus closer to the ideal program we want to return to the user.

### Rewriting the original program:


<span style="font-variant:small-caps;">Syren</span>'s first rewrite replaces the instance IDs, which are constants used repeatedly in multiple calls, with the output of a ternary expression. The following rewrites pull the first call to `ec2.StopInstances` and the call to `ec2.DescribeInstanceStatus` out of the if-statement, since it is identical in both branches. These rewrites make the program smaller and remove repeated API calls, two of <span style="font-variant:small-caps;">Syren</span>'s optimization goals.

<span>
  <img 
    style="display: block; margin: auto; background-color: #fffbf0;" 
    width="550em"
    src="./code_snippet_12_0.png"
    alt="A code snippet containing with the following source code:
    λ br.
    if br == 1 {
      let x_1_1 = ec2.StopInstances(instanceIds=['i-12345'], force=false)
      let x_1_2 = ec2.DescribeInstanceStatus(instanceIds=['i-12345'])
    } else {
      let x_2_1 = ec2.StopInstances(instanceIds=['i-54321'], force=false)
      let x_2_2 = ec2.DescribeInstanceStatus(instanceIds=['i-54321'])
      let x_2_3 = ec2.StopInstances(instanceIds=['i-54321'], force=true)
    }
    "
  />
  <img 
    style="display: block; margin: auto;" 
    src="./arrow.png"
    alt="An arrow pointing down"
    width="35em"
  />
    <img 
    style="display: block; margin: auto; background-color: #fffbf0;" 
    width="550em"
    src="./code_snippet_12_1.png"
    alt="A code snippet containing with the following source code:
    λ br.
    let x_0 = (br == 1) ? ['i-12345'] : ['i-54321']
    let x_1 = ec2.StopInstances(instanceIds=x_0, force=false)
    let x_2 = ec2.DescribeInstanceStatus(instanceIds=x_0)
    if !br == 1 {
      let x_2_3 = ec2.StopInstances(instanceIds=x_0, force=true)
    }
    "
  />
</span>

<span style="font-variant:small-caps;">Syren</span> also aims to remove all usages of `br`, since it is an artificial variable with no real semantic meaning. To eliminate `br` in the ternary expressions, we need to replace the conditional expressions `br==1` with another expression that does not use `br`. There are two ways to achieve this: either introduce a new input parameter that takes the value of the expression, or synthesize a function that will eventually evaluate to the conditional expression value.

The first usage of `br` is removed by introducing an input parameter: <span style="font-variant:small-caps;">Syren</span> replaces all usages of the expression `(br==1) ? ["i-54321"] : ["i-12345"]` with `i_0`. Within the conditional branches, <span style="font-variant:small-caps;">Syren</span> also replaces the usages of the value the expression evaluates to, considering the condition. This results in the following program:

<span>
  <img 
    style="display: block; margin: auto; background-color: #fffbf0;" 
    width="478em"
    src="./code_snippet_30.png"
    alt="A code snippet containing with the following source code:
    λ br.
    let x_0 = (br == 1) ? ['i-12345'] : ['i-54321']
    let x_1 = ec2.StopInstances(instanceIds=x_0, force=false)
    let x_2 = ec2.DescribeInstanceStatus(instanceIds=x_0)
    if !br == 1 {
      let x_2_3 = ec2.StopInstances(instanceIds=x_0, force=true)
    }
    "
  />
  <img 
    style="display: block; margin: auto;" 
    src="./arrow.png"
    alt="An arrow pointing down"
    width="35em"
  />
    <img 
    style="display: block; margin: auto; background-color: #fffbf0;" 
    width="478em"
    src="./code_snippet_31.png"
    alt="A code snippet containing with the following source code:
    λ br, i_0.
    let x_1 = ec2.StopInstances(instanceIds=i_0, force=false)
    let x_2 = ec2.DescribeInstanceStatus(instanceIds=i_0)
    if !br == 1 {
      let x_2_3 = ec2.StopInstances(instanceIds=i_0, force=true)
    }"
  />
</span>


The final rewrite for this example replaces the last conditional that depends on `br`. The user decided whether to make the second call to `StopInstances` depending on the outcome of the previous call to `DescribeInstanceStatus`: if the instance doesn't show as `"stopped"` yet, then they force it to stop. This makes the rewrite a little trickier: to replace the condition, we need to uncover the admin's reasoning when they executed the task. To uncover this "hidden" behavior, <span style="font-variant:small-caps;">Syren</span> will replace `!br==1` with the output of a new function `φ`. `φ` represents the hidden computations that, in this case, <span style="font-variant:small-caps;">Syren</span>'s user performed in their head. Since we don't know what previous information the user used, `φ` takes as input all variables in scope at this point in the program. `φ` remains undefined for now, so we declare the program is parametric on its implementation in the first line with `Λ φ.`.

<span>
  <img 
    style="display: block; margin: auto; background-color: #fffbf0;" 
    width="479em"
    src="./code_snippet_40.png"
    alt="A code snippet containing with the following source code:
    λ br, i_0.
    let x_1 = ec2.StopInstances(instanceIds=i_0, force=false)
    let x_2 = ec2.DescribeInstanceStatus(instanceIds=i_0)
    if !br == 1 {
      let x_2_3 = ec2.StopInstances(instanceIds=i_0, force=true)
    }
    "
  />
  <img 
    style="display: block; margin: auto;" 
    src="./arrow.png"
    alt="An arrow pointing down"
    width="35em"
  />
    <img 
    style="display: block; margin: auto; background-color: #fffbf0;" 
    width="479em"
    src="./code_snippet_41.png"
    alt="A code snippet containing with the following source code:
    Λ φ. λ i_0.
    let x_1 = ec2.StopInstances(instanceIds=i_0, force=false)
    let x_2 = ec2.DescribeInstanceStatus(instanceIds=i_0)
    let c = φ(i_0, x_1, x_2)
    if c {
      let x_2_3 = ec2.StopInstances(instanceIds=i_0, force=true)
    }
    "
  />
</span>


### Example-based synthesis of hidden functions

Of course, this program is only useful if we can provide an implementation `f` for `φ` for which the program can perform the task. This is where example-based synthesis comes in.
During the rewrite process, we maintain a mapping from identifiers in the program to corresponding values in the traces. Then, we use these mappings to compute a set of input-output constraints that `f` must satisfy. Using these input-output examples, we can use an off-the-shelf synthesizer from examples to generate an implementation of `φ`. <span style="font-variant:small-caps;">Syren</span> supports [Rosette](https://emina.github.io/rosette/index.html) ([Torlak et al., Onward! 2013](https://dl.acm.org/doi/10.1145/2509578.2509586)) or [cvc5](https://dl.acm.org/doi/10.1145/2509578.2509586) ([Barbosa et al., TACAS 2022](https://doi.org/10.1007/978-3-030-99524-9_24)) as synthesizers from examples.

Looking at the program above and the traces that originated it side-by-side, we see that the first argument of `φ`, `i_0` corresponds to the instance ID in the traces, so its value must be `"i-12345"` to reproduce the behavior in Trace #1 or `"i-54321"` to reproduce Trace #2. The second argument of `φ`, `x_1` corresponds to the response of the first API call, `ec2.StopInstances`, and the third argument to the second API call, `ec2.DescribeInstanceStatus`. The output of `φ` is a boolean value that indicates whether the instance is `"stopped"` or not (which is `false` for the first trace and `true` for the second trace).

So, for the traces and program in this example, we know the implementation of `f` must be such that:

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

We encode these input-output constraints into a synthesizer from examples to generate the simplest logical expression that fits the behavior in the traces, and obtain the following implementation `f` for `φ`:

```syren
f := (i_0, x_1, x_2) -> x_2.InstanceState != "stopped"
```

Substituting `φ` for `f` yields a program that is correct by construction. Since only the last input is used by `f`, it may be called using that input only.


<span>
  <img 
    style="display: block; margin: auto; background-color: #fffbf0;" 
    width="479em"
    src="./code_snippet_50.png"
    alt="A code snippet containing with the following source code:
    Λ φ. λ i_0.
    let x_1 = ec2.StopInstances(instanceIds=i_0, force=false)
    let x_2 = ec2.DescribeInstanceStatus(instanceIds=i_0)
    let c = φ(i_0, x_1, x_2)
    if c {
      let x_2_3 = ec2.StopInstances(instanceIds=i_0, force=true)
    }
    "
  />
  <img 
    style="display: block; margin: auto;" 
    src="./arrow.png"
    alt="An arrow pointing down"
    width="35em"
  />
    <img 
    style="display: block; margin: auto; background-color: #fffbf0;" 
    width="479em"
    src="./code_snippet_51.png"
    alt="A code snippet containing with the following source code:
    λ i_0. 
    let _ = ec2.StopInstances(instanceIds=i_0, force=false)
    let x_2 = ec2.DescribeInstanceStatus(instanceIds=i_0)
    let c = f(s)
    if c {
      let _ = ec2.StopInstances(instanceIds=i_0, force=true)
    }
    where
    f := (x) -> x.InstanceState != 'stopped'
    "
  />
</span>

This final program executes the task described at the beginning!

## Beyond the example: search over a library of rewrites

<span style="font-variant:small-caps;">Syren</span> has a library of rewrite rules to apply to programs that includes a lot more than the ones used in the example.
Rewrites fall into two categories:


> __Refinement rules__ are simple structural transformations. These might lift identical statements out of conditionals or replace constants with parameters. They are correctness-preserving by construction and don't require synthesis. They uncover the program's control flow in a way that explains the observed functions.


> __Synthesis rules__ introduce hidden functions. They replace expressions with fresh calls to unknown functions ϕ, which are later synthesized using synthesis by example. These rules apply only if a valid implementation of ϕ exists that preserves trace behavior.


All rewrite rules are defined as patterns: if at some point the program matches a pattern defined as the start form of the rule, then the rule can be applied to the program. As an example, below is the definition of the first rewrite rule shown in the example above, that extracts an identical expression \\(\mathcal{R}\\) from both the then and the else branch of a conditional. \\(\mathcal{R}\\), \\(\mathcal{S}\\), \\(\mathcal{T}\\), \\(\mathcal{U}\\), and \\(\mathcal{V}\\) are arbitrary sequences of instructions in the program.

<span>
  <img 
    style="display: block; margin: auto;" 
    src="rewrite.png"
    alt="Figure showing a rewrite rule: a pattern with abstract constructs on the left, and the resulting pattern on the right."
    width="220em"
    style="margin: 1%"
  />
</span>

When the program <span style="font-variant:small-caps;">Syren</span> is considering has the structure on the left, the rule applies, and the program is rewritten with the structure on the right.


At any stage of the rewrite process, many rules can be applied to the program, too many to try them all. Instead, <span style="font-variant:small-caps;">Syren</span> performs a cost-directed search, using a cost function that penalizes undesirable program characteristics.
The cost functions in <span style="font-variant:small-caps;">Syren</span> prefer smaller, more general, and human-readable programs.
The paper implements two concrete cost functions that illustrate how different notions of "simplicity" lead to different outcomes.


The first, \\(\chi_{\mathrm{syn}}\\), follows the widely used Occam's razor principle, and favors purely syntactic simplicity: it assigns a weighted penalty to every statement, every parameter, and every use of the synthetic variable `br`.
\\(\chi_{\mathrm{syn}}\\) produces a fine-grained score that distinguishes most programs from one another, giving the search a clear signal at nearly every step.


<span style="font-variant:small-caps;">Syren</span> implements a second cost function, \\(\chi_{\mathrm{T}}\\), which takes a more semantic view of the programs: rather than counting syntactic elements, it measures how much each API call is reused across the input traces. A statement executed many times, such as an API call inside a loop shared across traces, contributes more reuse and therefore incurs lower \\(\chi_{\mathrm{T}}\\) cost than the same calls written out redundantly in separate branches. It also penalizes branches that only reproduce a single input trace, treating them as corner cases that suggest the program has not yet generalized. In practice, \\(\chi_{\mathrm{T}}\\) is worse at directing the search than \\(\chi_{\mathrm{syn}}\\), because it is coarser, meaning that more programs have the same score. Both metrics hit similar solve rates (72% vs. 70%), but \\(\chi_{\mathrm{syn}}\\) generates programs that are easier to read.


The cost function does more than rank programs after applying rewrites. It actively controls which rewrites to apply at every step of the search. <span style="font-variant:small-caps;">Syren</span> treats the two types of rewrites differently. At each step, it first scans all applicable refinement rules and greedily applies whichever one produces the greatest reduction in cost, repeating this until no refinement rule can lower the cost any further. Only then does it consider synthesis rules, again selecting the one with the largest expected cost reduction and invoking the example-based solver to check whether a valid implementation exists for any newly introduced computation. This ordering means the solver is called as sparingly as possible. The cheap structural rewrites are exhausted first, so that by the time synthesis is attempted, the program is already as simple as refinement alone can make it.
As with the cost function itself, <span style="font-variant:small-caps;">Syren</span>'s source code provides predefined search strategies but allows users to define their own.


# Final Thoughts


<span style="font-variant:small-caps;">Syren</span> is, to our knowledge, the first approach to synthesizing programs that combine side-effecting API calls, control flow, and hidden pure functions purely from execution traces: no annotations, no natural language, no hand-crafted examples.

In [the paper](https://arxiv.org/pdf/2504.14480), we showcase <span style="font-variant:small-caps;">Syren</span>'s practical applicability. It synthesizes correct, human-meaningful scripts for 54 real-world tasks, including cloud automation, filesystem manipulation, and document editing scripts, collected from custom tasks, existing [AWS Automation Runbooks](https://docs.aws.amazon.com/systems-manager-automation-runbooks/latest/userguide/automation-runbook-reference.html), [Blink Automations](https://www.blinkops.com/), and [related work from Guo et al. at PLDI 2022](https://dl.acm.org/doi/10.1145/3519939.3523450). The underlying example-based synthesizer generates non-trivial data transformations, that allow <span style="font-variant:small-caps;">Syren</span> to uncover more intricate computations, not visible in the traces. <span style="font-variant:small-caps;">Syren</span> introduces control structures like if-then-else conditionals and retry-until loops, and successfully synthesizes 39 out of 54 scripts in under 5 minutes. 

Though powerful, the synthesis of data transformations is <span style="font-variant:small-caps;">Syren</span>'s main bottleneck: when the hidden functions require complex manipulation of JSON data, the underlying example-based synthesizer can struggle to find the right expression. Improving <span style="font-variant:small-caps;">Syren</span>'s performance will likely require more specialized grammars or solvers for this domain.
There is another limitation worth acknowledging beyond performance: the quality of <span style="font-variant:small-caps;">Syren</span>'s programs depends heavily on having sufficiently diverse traces. Two very similar traces may provide too little signal for the synthesis-by-example solver to distinguish the right hidden function from a degenerate one.
Looking ahead, there are natural extensions to explore. Real-world traces are recorded from humans, and humans are inconsistent. An action a user took once in an unusual mood may not reflect the general pattern they want to automate, but <span style="font-variant:small-caps;">Syren</span> currently tries to explain every trace it's given, treating all of them as equally intentional. A natural extension would be allowing <span style="font-variant:small-caps;">Syren</span> to identify and discard outlier traces, synthesizing a program that fits the majority of the observed behavior rather than demanding a perfect explanation for all of it.

As systems become more API-driven and observability tooling improves, the resulting raw logs become more abundant. <span style="font-variant:small-caps;">Syren</span> takes a step towards a future where that data doesn't just sit in a dashboard waiting to be analyzed, but actively gets turned into automation. Instead of asking users to articulate what they want, we can just watch what they do.


<!-- Style: -->
<style>
pre > code {
  font-size: 100%;
}

pre , code {
  font-size: 77%;
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

<!-- After applying these two rules, the intermediate program has cost~44: -->

<!--


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

| Header 1   |   Another header here | This is a long header |
| :--------- | --------------------: | :-------------------: |
| Some data  |        Some more data | data \\( \epsilon \\) |
| data       | Some _long_ data here |       more data       |
| align left |                 right |        center         |

You use the `:` specifier in the table header-body splitting line to
specify whether the particular column should be left, center, or right
aligned. All the standard markdown elements continue to work within
the table, so feel free to use them.

# Finale {#finale}

Finally, you're at the end of your blogpost! Your name will appear
again at the end automatically, as will the committee members who will
(hopefully) approve your blogpost with no changes! Good luck! -->
