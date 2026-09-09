+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "A Model of Regulated Execution"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2026-04-27

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Systems"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
# Consider these similar to keywords specified for a research paper.
tags = ["computer-architecture", "execution-model"]

[extra]
author = {name = "Jennifer Brana", url = "" }
# The committee specification is  a list of objects similar to the author.
committee = [
    {name = "Myra Dotzel", url = "https://www.andrew.cmu.edu/user/mdotzel/"},
    {name = "Justine Sherry", url = "https://www.justinesherry.com/"},
    {name = "Phillip Gibbons", url = "https://www.cs.cmu.edu/~gibbons/"}
]
+++


# Introduction

Computer architecture determines how programs execute in hardware—how work unfolds over time and across resources. 
Most readers are familiar with processors through the _Von Neumann model_, where programs are executed as sequences of instructions. 
In this view, execution appears strictly ordered: instructions are fetched, executed, and their results are written back one after another. 

Modern systems, however, look very different. 
Architectures such as superscalar out-of-order processors, GPUs, dataflow machines, and domain-specific accelerators depart from this simple model in significant ways. 
Despite these differences, they can be understood as making different choices about three key questions: 
when work enters the machine, when it executes, and when its results become visible.

These choices matter because they shape how programs actually run. 
Some architectures try to expose as much parallel work as possible, admitting and executing many operations at once. 
Others are more conservative, limiting how much work enters the system or delaying when results become visible in order to control resource usage or enforce ordering. 
As a result, performance, efficiency, and scalability depend on how a system manages work as it moves through the machine.

Despite this diversity, there is no common way to compare these design choices across architectures. 
Most execution models are studied in isolation, and system behavior is explained in terms of specific mechanisms rather than a shared structure. 
This makes it difficult to compare designs, transfer insights across systems, or explain performance in a principled way.

**This work presents a general model for comparing runtime and state trade-offs across architectures.**
At a high level, we observe that all of these systems are solving the same problem: 
**managing work while it is active inside the machine**.

Understanding execution is challenging because it emerges from the interaction of software, interfaces, and hardware. 
Software defines what work is available, interfaces define when operations are allowed to execute and become visible, and hardware implements these rules under finite resources. 
Existing approaches typically separate these concerns: formal models describe correctness, while performance models describe efficiency. 
However, they do not explain how correctness constraints shape performance. 
In practice, many bottlenecks arise not from a lack of resources, but from how systems enforce correctness—for example, by restricting when results can become visible.

Another limitation is that most models focus on how work executes, but not how it is managed while it is in flight. 
Real machines must track partially completed operations under finite resources, yet these mechanisms are often studied separately. 
As a result, execution is understood as a collection of components rather than as a unified process.

We introduce **regulated execution**, a model that treats execution as the management of in-flight work. 
In this view, operations enter the system, remain active while they execute, and eventually complete when their results become available. 
Throughout this process, the machine must track and coordinate these operations using limited hardware resources. 
**Architectures can therefore be understood as regulating how work evolves within the machine**.

To make this concrete, we introduce **Stateflow**, a framework for describing how architectures regulate the existence and movement of work during execution. 
Under this view, **systems that appear very different—from superscalar processors to GPUs and dataflow machines—can be understood as different choices within a common execution structure**.


![Performance–live-state tradeoff across execution models executing Jacobi-1](figures/results/pareto_jacobi1.png)

**Contributions.**
This work makes the following contributions:

- **Regulated execution**, a model that describes execution as the evolution of in-flight work under correctness and resource constraints.
- **Stateflow**, a framework for describing architectures in terms of how they admit, execute, and complete work.
- A **cross-paradigm simulator** that enables direct comparison of architectures within a unified performance--state tradeoff space.

Using this framework, we place different architectures within a common performance--state tradeoff space, shown in Figure 1. 
Allowing more work to be active can improve performance, but it also requires maintaining more state and often changes what limits execution. 
We find that bottlenecks do not arise accidentally—they follow directly from how architectures enforce correctness and manage in-flight work.

Using the Stateflow framework, we show how architectural choices governing the exposure of work determine both the amount of live-state maintained in the system and the performance that can be achieved. This allows us to model diverse architectures and place them at different points along a common performance–state tradeoff space illustrated in Figure 1. Common bottlenecks arise, showing that architectural design does not remove constraints but determines which one limits performance.

Taken together, these contributions suggest a different way to think about computer architecture.

# Regulated Execution

This section introduces a structured explanation of execution systems
that identifies the underlying process, invariants, and principles governing 
them. 
The derived model(Figure 4) explains how systems behave, 
allowing us to reason about performance and efficiency across machines. 

## Execution Dynamics

We first describe how execution proceeds as a process of managing live work inside the machine.

**Live State.**
At any point in time, the machine holds a set of active work: operations that have been brought into the system but have not yet completed and released their resources. This includes work that is ready to execute, currently executing, or finished but not yet committed. We refer to this as _live state_. It represents everything the machine must track to keep execution moving forward.

**Execution Policies.**
Execution is governed by three interacting policies that control how this live state evolves:

- **Admission**: determines what work is allowed to enter the machine. Bringing in more work increases live state.
- **Fire**: determines which admitted operations execute. Execution consumes resources and transforms state, but does not change how much state exists.
- **Retire**: determines when work is completed, its results are made visible, and its state is released. Retirement reduces live state.

These policies together regulate how much work the machine is carrying at any time. If work enters faster than it completes, live state builds up; if work completes faster than it enters, the machine runs out of work. Sustained execution requires balancing these forces.

The simplest system, shown in Figure 2A, tightly couples all three policies. Work is only admitted when it can immediately execute, and results become visible as soon as they are produced. This creates a strict pipeline with minimal live state: a single program counter tracks the next instruction, and execution proceeds one operation at a time through a single stage that fetches, executes, and completes in lockstep.

**Figure 2: Pipeline construction.**

**(a)** In-order von Neumann (InOvN) pipeline: execution follows the strictest order, therefore the pipeline tracks the least.  
![InOvN pipeline](figures/model/InOvN_Pipeline.png)

---

**(b)** Pipeline with added admit stage to enable relaxed admission. 
![Admit pipeline](figures/model/admit_pipeline.png)

---

**(c)** Pipeline with added retire stage to enable speculation.
![Retire pipeline](figures/model/retire_pipeline.png)

## Execution Requirements

We now define two essential requirements of execution: correctness and stability.

Correctness constrains _what_ executions are permitted (semantic validity);
stability constrains _how_ executions can proceed on finite hardware
(physical viability).

### Correctness.
A program specifies a partial causal order over dynamic operations corresponding 
to true data and control dependencies.
A correct execution must respect this causality: no operation may consume
a value before its producer has produced it, and no execution may make an
effect visible that violates the program’s causal order.
Correctness therefore restricts the allowable trajectories of execution,
but does not determine the physical realizability.
In this view, correctness constraints do not only restrict firing, 
but also shape how work can be admitted and completed, and therefore 
directly influence performance.

**Implication for Optimizations**
Modern out-of-order (OoO) processors exploit a key insight: 
correctness does not require operations to execute in program order, 
only that data dependencies are respected and results become visible in a valid order.

This separation enables two optimizations.

First, OoO processors admit instructions early. 
They place instructions into structures such as the instruction window 
as soon as their dependencies are known, without waiting for inputs to be ready. 
This corresponds to _relaxed admission_: operations become live before they can execute. 
Execution is then scheduled dynamically—an instruction fires as soon as its inputs arrive—exposing parallelism not visible in program order. 
Correctness is preserved because execution still waits for inputs.

Second, OoO processors use speculation. 
They execute instructions before it is known whether they are needed, 
for example by predicting branches or memory dependencies. 
These speculative results are held in structures such as the reorder buffer 
and are not made visible immediately. 
This corresponds to separating execution from _retirement_: 
results are computed early but only published once validated. 
Incorrect speculation is discarded.

Together, relaxed admission and speculation allow execution to move ahead of program order, 
while correctness is enforced at retirement when results become visible.

![Closed-loop interpretation of regulated execution](figures/model/regexec_fullpipeline.png)

*Figure 4: Closed-loop interpretation of regulated execution. Work is admitted into live-state, scheduled subject to finite execution bandwidth, fired, and eventually retired. Admission is constrained by finite live-state capacity, inducing feedback from occupancy to exposure, while scheduling is constrained by finite execution bandwidth, inducing feedback from resource limits to firing. Together these feedback paths make execution a closed-loop dynamical system over live-state.*

### Stability
Real machines operate under finite resources, imposing bounds on live-state and execution bandwidth. These bounds act as regulators on the execution dynamics in Figure 4, converting it into a closed-loop system.
A bounded state capacity limits how much work can be live at once, forcing admission to slow or stop as the machine fills. The same applies for PE or execution bandwidth limits.
Stability therefore requires not just bounding state, but ensuring progress: admitted work must eventually leave the system through retirement or discard, rather than accumulating indefinitely.

# Stateflow Execution Model

This section introduces _Stateflow_, a framework for modeling how 
machines regulate execution.
We represent systems using a three-layer system stack as shown 
in Figure 3.
The stack includes an _architectural contract_ that an architectural contract that specifies what the hardware must guarantee, 
a _program model_ that provides an abstraction for software to specify work to the machine, 
and an _abstract machine model_ that shows how the hardware actually instantiates this process under finite resources. 
Architectural policies allow specifying concrete machines within this framework.
Different architectures correspond to different choices of these policies, which we demonstrate later in Table 1.
Together, these components connect program structure, architectural policy, and hardware behaviour into a single model of execution.

![Stateflow system stack.](figures/systemstack.png)

*Figure 3: Stateflow system stack.*

## Architectural Contract

The architectural contract defines the interface between software and hardware. 
It specifies what a program may request and the conditions under which execution is valid.

Execution is governed by two kinds of constraints.

**Temporal constraints** determine _when_ execution may proceed.  
An operation cannot execute until its inputs are available, and results cannot be made visible until correctness conditions are satisfied.

**Spatial constraints** determine _whether_ execution may proceed.  
An operation requires resources—such as storage, bandwidth, or compute—and must wait if they are unavailable.

These constraints appear in all systems. 
For example, computation cannot begin until inputs are ready, and cannot continue without sufficient memory or bandwidth. 
Architectures differ in how they enforce these constraints, leading to different performance outcomes.

### Three-Stage Contract

We describe execution using three stages: _Admit_, _Fire_, and _Retire_.  
Admit introduces work into the machine, Fire performs computation, and Retire completes work and exposes its results.

**Admit (State Allocation).**

Admission makes an operation live by allocating state.

_Spatial constraint (capacity)._  
An operation is admitted only if sufficient state is available.

_Temporal constraint (drainability)._ 
Admitted work must be able to complete. This is enforced through _producer-closed admission_, which ensures that operations are only admitted when their completion can be supported by existing or admissible work.

**Fire (Execution).**

Firing executes an admitted operation.

_Temporal constraint (dependencies)._  
Execution requires all inputs to be available.

_Spatial constraint (bandwidth)._ 
Execution proceeds only if compute and data movement resources are available.

**Retire (Publication).**
Retirement completes an operation, releases its state, and makes its results visible.

Before retirement, results may exist internally but are not observable. 
Retirement determines when results become visible, enforcing both synchronization and isolation.


## Program Model

Stateflow introduces a novel program graph abstraction that separates the conditions 
for _state allocation_, _execution_, and _publication and state deallocation_, 
allowing the program to explicitly specify how operations enter and leave live-state. 
This exposes the amount and lifetime of state required to sustain execution, 
allowing reasoning about whether execution fits within a finite capacity (boundedness) and whether all admitted work can complete (drainability).

We represent a program as a directed graph of operations and
dependencies. 

**Nodes.**
A program is defined as a finite set of operations O.
An operation denotes a unit of work that may occupy machine state.
Operations may be primitive instructions or
structured _super-operations_ that encapsulate subgraphs 
(see Figure 6).

**Edges.**
An operation's edges define the conditions that must be satisfied for it to move through the stages of the architectural contract.
Each edge acts as a gate that blocks later stages until its condition is met.

Figure 5 illustrates this behaviour.
Even if its inputs are ready, the operation cannot enter the machine until its admit condition is satisfied.
Once admitted, it occupies state but cannot execute until its fire conditions are met.
Execution produces results immediately, but those results remain internal until retire.
Only then does the operation complete and publish.

| | |
|---|---|
| ![Legend](figures/legend.png) | ![Operation](figures/program/operation.png) |

*Figure 5: Operation in Stateflow.*

**Super-operations.**
Super-operations encapsulate structured regions of a program and define
_scoped boundaries_ for admission and retirement. Externally, a
super-operation behaves as a single unit: it is admitted when its incoming
dependencies are satisfied, and it retires only after all internal work has
completed. Internally, however, it may contain a rich dependency structure that
can execute according to local rules.

To ground this idea, consider the dense matrix-vector multiplication (DMV)
kernel in Figure 6. Each iteration of the outer loop computes one output
element independently.

```text
for i = 0 ... m-1:
    w = 0
    for j = 0 ... n-1:
        w += A[i,j] * B[j]
    Z[i] = w
```

![Super-operation representation](figures/program/superoperation.png)

*Figure 6: Dense matrix-vector multiplication (DMV) and its super-operation representation. Left: compact program form. Right: each row is a super-operation with admission (blue) and retirement (orange) dependencies. Internal operations execute according to local dataflow, exposing parallelism within each row while preserving controlled visibility across rows.*

Figure 6 shows how this structure is captured using
super-operations for a 3x3 instance. Each shaded region corresponds to
one iteration of the outer loop (one row computation).

The blue edges at the top of each region represent _admission
dependencies_. They determine when a row-level super-operation may begin. Once
admitted, the internal graph becomes active: the multiply and add operations
that form the dot product execute as soon as their inputs are available,
independently of other rows.

The orange edges at the bottom represent _retirement dependencies_. A
super-operation retires only after all internal operations complete and the
final result (e.g., Z[i]) is produced. At that point, the result becomes
visible and the resources associated with the region are released.

This separation is the key idea. The super-operation presents a simple interface
to the rest of the program—admit as a unit, retire as a unit—while internally
exposing fine-grained parallelism. As a result, execution can be organized
hierarchically: ordering and visibility are enforced at region boundaries,
while parallelism is exploited within regions.

In practice, super-operations let us choose the level at which we enforce
ordering and visibility. In DMV, we group work at the row level: each row
executes internally with full dataflow parallelism, while ordering is enforced
only across rows. Different groupings would expose different tradeoffs between
parallelism and the amount of live state that must be maintained.

At the highest level, the program itself is a super-operation: it is
admitted at start and retires at completion. All internal structure can
be understood as nested super-operations, each defining a local unit of
execution and visibility.


## Visibility, Speculation, and Publication

The program separates execution from publication by treating retirement as the point at which results become globally observable. Correctness is enforced by constraining publication rather than execution: memory ordering, for example, is captured through retire--\>retire constraints, ensuring results appear in the required order even if they execute out of order. This decoupling allows execution to proceed ahead of full knowledge, with correctness checked only at publication.

Under this view, speculation is simply execution prior to retirement. Operations may execute before all dependencies or control conditions are resolved, carrying uncertainty as part of their live state, as long as these uncertainties are resolved before results become visible. This shifts correctness enforcement to publication, allowing forward progress without stalling on unresolved conditions.

This motivates delaying and structuring publication. By organizing retirement into scoped or distributed domains, the system avoids a single global visibility bottleneck. Stateflow makes this explicit: the program graph encodes publication constraints through retirement edges and scope boundaries, defining when results become visible and where their effects propagate, enabling localized synchronization, relaxed consistency, and containment of speculative effects.

# Result: A Uniform Design Space

Stateflow reveals that diverse architectures are not fundamentally 
different mechanisms, but instances of a small number of policy 
choices governing admission, firing, and retirement. 
In Table 1, we show how a range of architectures can be expressed as distinct combinations of these policies.

| Prior Architecture | Exposure Granularity | Admission Policy | Firing Policy | Retirement Policy | Bottleneck |
|--------------------|---------------------|------------------|---------------|-------------------|------------|
| Pure Von Neumann (vN) | Instruction | CF | CF | CF (In order) | Control-flow admission |
| Out-of-Order (OoO) vN | Instruction | Relaxed CF | DF | CF (In order) | Retirement serialization |
| OoO w/ OoO Retire[^ooo-commit] | Instruction | Relaxed CF | DF | DF (As-ready) | State capacity |
| Pure Dataflow | Instruction | DF | DF | DF (As-ready) | State capacity |
| vN w/ Threads | Thread / Instruction | Relaxed CF | CF (outer), CF (inner) | CF (Join/async) | Control-flow admission |
| OoO w/ Threads | Thread / Instruction | Relaxed CF | CF (outer), DF (inner) | CF (Join/async) | Retirement serialization |
| WaveScalar[^wavescalar] | Wave / Instruction | Relaxed CF | DF | CF (Wave-ordered) | Retirement serialization |
| Tyr[^tyr] | Region / Instruction | Per-region Relaxed CF | DF | DF (Independent) | State capacity |

*Table 1: Architectures expressed using the Stateflow model, including dominant bottleneck.*

To compare performance across architectures, we instantiate Stateflow as a 
cross-paradigm simulator, 
following a limit study methodology[^ddg],[^lam],[^ilp-limits]. 
Given a program trace, we evaluate each policy configuration in terms of 
runtime and peak live state. 
Figure 1 plots runtime versus live state, exposing the achievable 
performance--state tradeoff.

The figure reveals a clear structure. 
Architectures differ in how much work they allow to be live at once, as determined by their admission, execution, and retirement policies. Allowing more live 
work generally reduces runtime, but requires substantially more state, with diminishing returns as systems approach ideal performance.
Architectures differ in where they appear in this tradeoff space—some lie near ideal, 
while others incur excess state without proportional performance gains, reflecting policy 
inefficiency rather than fundamental limits imposed by the program.

More over, the figure demonstrates that exposing more work does not simply improve 
performance. 
Instead, it changes what limits performance. 
As architectures permit more concurrent work, the dominant bottleneck shifts in a 
consistent progression: from admission, to retirement, to state capacity.

This behaviour is visible across different execution styles, including out-of-order, 
dataflow, and scoped execution models. 
In out-of-order processors, allowing more work to be live through relaxed 
admission improves performance initially, but quickly shifts the bottleneck 
to retirement, where results must still commit in order.
In particular, the retirement bottleneck in out-of-order processors arises directly 
from enforcing correctness through ordered visibility of results. 
In dataflow architectures, removing ordered retirement allows operations to 
complete as soon as they are ready, but requires maintaining a much larger 
volume of in-flight state, making performance limited by the capacity of live state. 

Scoped execution models mitigate this effect by limiting how widely results must 
be made visible. 
Instead of requiring all operations to commit in a single global order, they group 
work into smaller regions that can complete locally. 
For example, systems such as WaveScalar or Tyr allow operations within a region 
to retire once their local dependencies are satisfied, without waiting for unrelated 
work elsewhere in the program. 
This reduces global serialization incurred by OoO while avoiding the need to 
keep all in-flight work live at once like dataflow.

Allowing more work to be live can therefore improve performance, but often shifts 
the bottleneck to retirement or increases the state required to sustain execution. 
Designs such as scoped execution partially mitigate this effect by localizing 
publication, reducing global serialization while avoiding unnecessary growth in live state.

This pattern appears across all of the architectures we evaluate in Table 1. 
Different policy choices tend to run into different limits, 
and these limits follow directly from how the system is designed. 
For example, restricting admission limits how much work can enter the machine, 
while enforcing ordered completion limits how quickly results can be made visible. 
These bottlenecks arise from the structure of the policies themselves, 
demonstrating how architectural design limits performance.


Taken together, these results show that performance is governed by a 
tradeoff between parallelism and live state, mediated by admission, 
retirement, and resource capacity. 
Architectural design does not remove these constraints—it determines 
whether performance is limited by admission, retirement, or state, 
and thus where the bottleneck lies. 
Computer architecture is therefore fundamentally the design of systems that 
regulate the exposure and lifetime of live computational state.

# Conclusion

This work introduced regulated execution and Stateflow, a framework for 
understanding execution as the management of live work under finite resources. 
Under this view, architectures that appear very different can be described 
using the same underlying structure, defined by how they admit work, execute it, 
and make results visible.

By placing these designs within a common framework, Stateflow reveals that 
architectural differences are not fundamentally about distinct mechanisms, 
but about different choices in how work is managed as it moves through the system. 
This provides a unified way to compare execution models, explain their behaviour, 
and reason about the tradeoffs they make. 


# Acknowledgements

This work was done in collaboration with Martha Kim, Olivia Hsu, and Nathan Beckmann.
I want to thank my Writing Skills committee, Justine Sherry, Phil Gibbons, and Myra Dotzel, for their suggestions and feedback on this post. I also want to thank Jonathan Balkind for providing invaluable feedback on this work.

## References

[^ooo-commit]: A. Cristal, D. Ortega, J. Llosa, and M. Valero, “Out-of-Order Commit Processors,” in HPCA, 2004. url: https://doi.org/10.1109/HPCA.2004.10008.

[^wavescalar]: S. Swanson, K. Michelson, A. Schwerin, and M. Oskin, “WaveScalar,” in MICRO, 2003. doi: 10.1109/MICRO.2003.1253203.

[^tyr]: N. Agarwal, M. Fream, S. Ghosh, B. C. Schwedock, and N. Beckmann, “The Tyr Dataflow Architecture: Improving Locality by Taming Parallelism,” in MICRO, 2024. url: https://doi.org/10.1109/MICRO61859.2024.00089. 

[^ddg]: T. M. Austin and G. S. Sohi, “Dynamic Dependency Analysis of Ordinary Programs,” in ISCA, 1992. url: https://doi.org/10.1145/139669.140395.

[^lam]: M. S. Lam and R. P. Wilson, “Limits of Control Flow on Parallelism,” in ISCA, 1992. url: https://doi.org/10.1145/139669.139702.

[^ilp-limits]: M. A. Postiff, D. A. Greene, G. S. Tyson, and T. N. Mudge, “The Limits of Instruction Level Parallelism in SPEC95 Applications,” SIGARCH Computer Architecture News, 1999. url: https://doi.org/10.1145/309758.309771.

