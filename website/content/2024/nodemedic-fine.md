+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "NodeMedic-FINE: Automatic Detection and Exploit Synthesis for Node.js Vulnerabilities"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2024-09-06

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Security"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
# Consider these similar to keywords specified for a research paper.
tags = ["Fuzzing and Vulnerability Discovery", "Program analysis", "Web security"]

[extra]
# For the author field, you can decide to not have a url.
# If so, simply replace the set of author fields with the name string.
# For example:
#   author = "Harry Bovik"
# However, adding a URL is strongly preferred
author = {name = "Nuno Sabino", url = "https://cmuportugal.org/students/nuno-sabino/" }
# The committee specification is simply a list of strings.
# However, you can also make an object with fields like in the author.
committee = [
    {name="Bryan Parno", url="https://www.andrew.cmu.edu/user/bparno/"},
    {name="Lujo Bauer", url="https://users.ece.cmu.edu/~lbauer/"},
    {name="Daniel Ramos", url="https://danieltrt.github.io/"}
]
+++

This post describes a part of our work NodeMedic-FINE, an automated tool to find arbitrary command injection and arbitrary code execution vulnerabilities in Node.js packages. While I am the sole author of this blog post, the work it describes was done in collaboration with [Darion Cassel](https://darioncassel.me/), [Limin Jia](https://darioncassel.me/) and [Ruben Martins](https://sat-group.github.io/ruben/). A preprint of our paper is available [here](https://darioncassel.me/pdfs/nodemedic-fine-preprint.pdf).

# Introduction

## The Node.js ecosystem

The growing Node.js ecosystem is comprised of millions of JavaScript packages. Each package typically exposes a set of public APIs, which are also commonly called *entry points*. Once a specific package is imported (e.g. by other packages), its public API can be called with arbitrary arguments. While a minority of Node.js packages are used in the frontend, we focus on packages providing backend functionality.

## Arbitrary command injection and arbitrary code execution vulnerabilities in Node.js

As it has become more popular, the Node.js ecosystem has turned into an attractive target for attackers and prior work has shown that many packages in the Node.js ecosystem contain security vulnerabilities [1, 2, 3, 4, 5, 6].

Two of the most serious vulnerabilities that can be present in Node.js packages are Arbitrary Command Injection (ACI) and Arbitrary Code Execution (ACE) vulnerabilities, which allow attackers to execute commands or code on the system that runs the application.

In ACI vulnerabilities, **sources** of attacker-controlled inputs can influence the arguments to dangerous functions like *exec* or *spawn*, which execute the command given in the argument. With respect to ACE vulnerabilities, **sources** influence the arguments to functions like *eval* or the *Function* constructor, which take JavaScript code as a string and execute it as long as it is syntatically valid. These dangerous functions that should not be controlled by an attacker are commonly called **sinks**.

## Our attacker model

We assume that all arguments to entry points are potentially controlled by an attacker. While this may not apply to some packages where calls to entry points have arguments that are either hardcoded or come from a legitimate or trusted source, the large majority of vulnerabilities that we reported were acknowledged by the maintainers. We are currently responsibly disclosing the vulnerabilities we found to CVE (Common Vulnerabilities and Exposures) authorities - CVE is a list of publicly disclosed security flaws. Each of those can have a CVSS (Common Vulnerability Scoring System) which is a numerical score reflecting the severity of a vulnerability. We were already assigned 1 [CVE with a 7.3 / 10 CVSS score](https://security.snyk.io/vuln/SNYK-JS-NETWORK-6184371).

## Dynamic taint analysis

We are interested in finding whether a certain execution of an entry point call reveals a vulnerability, so we execute the target package many times with different inputs.
Dynamic taint analysis is a technique that allows us to know whether information from a **source** of attacker-controlled input like the arguments to the entry point is propagated to the arguments of dangerous functions like *exec* or *eval*. Such a propagation of information is also called a **flow**. We implement this technique by instrumenting the package code and extending primitive values like *strings* with extra information (commonly called **taint**) that signals whether the value can be controlled by the attacker or not. **Sources** are marked as tainted (i.e. influenced by the attacker) by default, and as the program execution progresses, operations on tainted values, like the concatenation of one constant string with a second string that comes from the attacker, create tainted results. In this example, the final string is at least partially controlled by the attacker. If we find that *eval* is called with tainted arguments, we report it as a flow!

Just because a flow is found, it does not mean that the flow represents a real vulnerability. In addition to many other reasons, an attacker may be able to control the arguments to *eval* but may still be unable to execute arbitrary code if it is impossible to make it syntatically valid. Another example could be that the attacker controls the name of a function that is dynamically generated, but the package sanitizes every character that should not belong to a function name according to the JavaScript syntax. Dynamic taint analysis helps us find "potential" vulnerabilities which we have to later confirm using other methods.

## Limitations of prior work and how we address them

Given that NPM is such a large ecosystem of packages and each of them can be individually vulnerable, we would like to analyse them all. 
There are several existing automated tools that identify ACI and ACE vulnerabilities, but most of these do not scale well and are not practical to use to analyse millions of packages like we did [7]. NodeMedic [8], a state-of-the-art system developed at CMU, is directly comparable to this work. NodeMedic was able to analyse 10,000 Node.js packages and found 155 flows but it was limited to sending a single hardcoded value as an argument to entry points. While this may be enough in many cases, the majority of entry points require their arguments to have specific types or structure. It remained to be seen how many more vulnerabilities could be discovered with a program exploration technique that aims to improve coverage. 

To avoid having to manually check all flows, many of those being false positives, there is also work on automatically synthesizing exploits to prove that an attacker can indeed execute malicious commands or code by leveraging the vulnerability. NodeMedic was able to synthesize working exploits for 108 of the analysed packages, including 102 ACI exploits and 6 ACE exploits. Note the much lower number of ACE exploits. The main difficulty in synthesizing ACE exploits is the fact that the final payload needs to be syntatically valid JavaScript, and current synthesis techniques fail to solve such contraints efficiently.

## NodeMedic-FINE

![NodeMedic-FINE diagram](./full_diagram.png)
*Figure 1 - NodeMedic-FINE diagram. In this post we only focus on the **fuzzer** and **enumerator** components. Refer to the paper for details about the remaining components.*


Our tool NodeMedic-FINE is an extension of NodeMedic with a set of self contained components that increase the number of flows and confirmed vulnerabilities significantly. Figure 1 presents a high-level description of the NodeMedic-FINE pipeline, from the target package to the generation of a candidate exploit that executes commands or code by leveraging found vulnerabilities.
First, we develop a coverage-guided, type- and object-structure-aware fuzzer for Node.js packages and integrate it with NodeMedic. 

Fuzzing is a software testing technique that involves sending automatically generated inputs to a program. Fuzzing tools like AFL [9] have been adapted for Node.js fuzzing [10]. These general-purpose tools predominantly generate byte sequences or strings, lacking intrinsic knowledge of JavaScript’s
rich type system. While effective in many scenarios, searching the string space is not sufficient to uncover a significant number of vulnerabilities. NodeMedic-FINE’s fuzzer is
type- and structure-aware and can generate inputs for a variety of types and with complex structure, like objects with specific attributes that have to be themselves objects.

Secondly, we develop another component which we call the **Enumerator** to aid in synthesizing ACE exploits. The Enumerator is responsible for, given a certain prefix, providing a number of alternative payload templates. It also provides great flexibility in the generation of ACE exploits. We will explain this process in detail later, but as a first example one could consider a function call like `eval("return " + attacker_input)`. In this case, the prefix is `return` and the enumerator takes that as an input and returns the right value for `attacker_input` such that the final argument to *eval* executes some code to prove that the vulnerability exists. This component was able to complete the majority of real world prefixes that we found, increasing the number of total ACE exploits by 15%.

# Fuzzer

In order to explore more execution paths, we implement a coverage-guided fuzzer for Node.js
packages, which aims to improve coverage by generating inputs of different types and with complex structure. In the following sections we will cover the design of the fuzzer in more technical detail, including a description of how different types are generated and how we refine input structure to further increase coverage.

## Fuzzing loop

![Fuzzer integration with rest of infrastructure](./fuzzer_diagram.png)
*Figure 2 - Fuzzer loop*

The fuzzer’s interactions with the rest of NodeMedic-FINE are shown in Figure 2. The fuzzer takes an input specification for the entry point parameter being
analyzed. The fuzzer generates inputs based on the specification and sends them to be executed. We instrument the code being tested such that it not only performs dynamic taint analysis, but it also extracts coverage information and the attributes accessed via field access operations (known as *getField* in JavaScript). Finally, the fuzzer refines its input specification by considering the newly accessed attributes. Using Figure 2 as an example, once **Feedback 1** is received by the fuzzer, which says that an attribute named `command` was accessed, the input specification for the next round is refined and the fuzzer will start being able to generate inputs with that attribute. This whole process is repeated until a time budget is exhausted.

## Input specification

Inputs are specified hierarchically by the following elements: 
a list of types that the input can have (types); 
a list of the number of samples taken for each type, where the i-th element specifies how many times the fuzzer sampled an input of the i-th type in the types list (sampled);
a list of coverage data for inputs of each type, where the i-th element represents the accumulated number of lines of code triggered by generated inputs of the i-th type in the types list (reward);
and a recursive specification of the structure of the final input (structure). 
The “Specification” boxes in Figure 2 are example specifications. The first box states that the first type in the list is an “Object” not yet sampled by the fuzzer. It sets the initial
reward for Objects to 200 and defines its structure as empty.

## Weight adjustment

Our fuzzer is coverage-guided: the amount of code executed by the previous inputs influences future input generation. 
The reward and sampled data in the specification decide the adjustable weight used for tuning input generation.
We provide an initial weight for each type, based on the observation that some types are more commonly expected by
Node.js package APIs than others. We aim to choose weights that increase the likelihood of generating inputs that trigger a
flow. We found that object inputs are most likely to result in flows, followed by
strings, booleans, and functions. We seed the reward field in initial input specifications to reflect the above observation.
These weights are dynamically adjusted after each fuzzing iteration based on coverage. 

The fuzzer only knows how effective each type is at improving coverage after it has tried them
all. At the same time, there is often a tradeoff between continuing to explore inputs of types that have already shown promise in the past and
trying out inputs of types that have not been explored much. This is known as the exploration-exploitation dilemma [11].
When deciding which new type to explore, we adopted an approach studied by prior work [12] based on a Poisson process. In our case, we consider each type t, with $$\lambda_t = \frac{reward_t}{sampled_t}$$

The higher this value, the more likely it is for type `t` to be generated by the fuzzer.
We consider the execution of a block of code to be an independent event. 
Each type distribution estimates the expected number of lines of code that we will execute, if we choose this type.
We sample from each type distribution and choose the type with
the largest sample value. Using this approach, it is more likely
for input types that were effective in the past to have higher
sample values and therefore to be chosen more frequently,
while still making it possible for types that were not effective
in the past to also be chosen eventually.

## Object reconstruction

According to the initial specification, the fuzzer starts by generating empty objects. For the fuzzer to generate objects with
useful structure, we extended NodeMedic’s taint instrumentation to keep track of the field names whenever a getField
operation is performed. This information is given as feedback to the fuzzer. At the end of each iteration, the input specification is updated to include newly discovered attributes. 
For example, in Figure 2 “Feedback 1” from the first run of the fuzzer states that it covered 117 lines of new code and accessed the field "command". The input specification is then updated to
“Specification 2”: with new coverage data and more detailed object structure. The fuzzer then generates a new input with the field "command" set to a random input.

# Enumerator

## Generating valid JavaScript payloads

Synthesizing syntactically valid JavaScript payloads is a key challenge for confirming ACE flows. 
The final argument to the sink needs to not only be valid JavaScript, but also execute the intended payload.  Consider the following example

```JavaScript
module.exports = {
    evaluate : function ( expr ) {
        var out = new Function(" return 2*( " + expr + ")");
        return out();
    }
};
```
Here we see a synthetic example that demonstrates these challenges. It shows an entry point called *evaluate* where the expected functionality is to return a number corresponding to double the value returned by evaluating the given argument as a mathematical expression. 
If we import the package and then use it as: `evaluate("1+1")` it returns 4. Notice that the expression to evaluate is given as a string and is interpreted as JavaScript.

A naive attempt to exploit could be `evaluate("1);console.log("VULN FOUND") //")`, with the initial characters of `1);` being the breakout sequence to finish the current expression. 
However, this exploit fails. The problem is that once JavaScript executes the instruction `return 2*(1);` it ignores what comes next, as the return statement just finishes the execution of the current function. 
A successful exploit needs to inject the payload before closing the current expression, like so: `evaluate('console.log("VULN FOUND")) //')`.
Note that the final argument to the *Function* sink in this case is `return 2*(console.log("VULN FOUND")) //)`. We close the parenthesis context right after the payload and before the comment
starts; otherwise an error would be thrown as the expression is syntactically invalid, as the open parenthesis would never be closed.

## Payload template

We now describe how the Enumerator constructs a target payload, which is the final string that will be passed to eval or the Function constructor. 
It differs from prior work like NodeMedic in its ability to construct a final payload that obeys all syntactic constraints and execute the intended statement. 
The Enumerator is given a prefix, such as `return 2*(` and outputs a number of alternative payload templates, each with a placeholder for an arbitrary statement to execute.
A payload template is a list where each element can have one of the following types:

-   Literal: A constant string, usually with syntactic connectors (e.g. a parenthesis `)`).
-   Payload: The placeholder for the payload.
-   Identifier: This is replaced with a valid variable name. It
is important that the final JavaScript expression does not use
undefined variables.
-   FreshIdentifier: This is replaced with a valid variable
name that was not used before, as some JavaScript expressions
have to use fresh variables.
-   GetField: This is replaced with any valid attribute.

An example payload template that the Enumerator outputs for the package and prefix described above is: `[Literal("return 2*("), Payload(), Literal(")"]`. Next we discuss
how payload templates are generated with some technical detail, but the reader can refer to the paper for more details.

## Graph representation

The Enumerator internally uses a graph representation for JavaScript syntax.
Each node is a symbol representing a JavaScript syntactic category, such as variable names and elements for the template described above.
The *root* is a node that represents the start of a new JavaScript expression. Collecting all symbols on a path from a node
to the *root* yields a valid payload template, which together with the prefix string can be instantiated to a valid JavaScript program. 
Thus the transition between node *A* and node *B* is only allowed if going to node *B* allows for a valid completion.
Using this graph, the Enumerator starts from the beginning of the prefix, searching for a node that matches the first symbol of the prefix. 
After finding it, it follows the transition based on the next symbol of the prefix until it finds the last symbol of the prefix. The Enumerator proceeds to use the graph edges to generate the template, performing a reachability analysis and outputing all paths that can reach the root of the graph from the
current nodes. Each path is a valid template to complete the prefix.

![Enumerator graph](enumerator.png)
*Figure 3 - Section of the graph representation of JavaScript syntax used by the Enumerator*

In the figure above, we show a part of the graph used by the Enumerator. Transitions from nodes are annotated with the constraints required to make such a transition syntatically valid.

# Evaluation

Our experiments were deployed via Docker containers on two Ubuntu 20.04 VMs, each with 12 cores and 32GB of RAM.
Packages were analyzed in parallel; one container per instance of NodeMedic-FINE analyzing a package. 
We repeated this process with several variants of NodeMedic-FINE configured with key components disabled to evaluate the effect of each component.

## Dataset gathering

We gathered **all** packages from _npm_ with at least 1 weekly download, resulting in a dataset of 1,732,536 packages. From this set, we analysed **all** 33,011 packages that contained calls to one of our supported sinks. To the best of our knowledge this was the largest dynamic taint analysis of ACI and ACE vulnerabilities in the Node.js ecosystem to date.

## How effective is type-aware fuzzing at uncovering ACE, ACI flows?

We ran our tool against the described dataset of 33,011 packages with calls to sinks. 

| Condition      | Extra                 | Missing               | Total | Exploited packages |
|:-------------- | ---------------------:|:---------------------:|       |                    |
| NodeMedic-FINE | -                     | -                     | 1966  | 597                |
| --ObjRecon     | 37                    | 74                    | 1929  | 590                |
| --Types        | 50                    | 195                   | 1821  | 596                |
| NodeMedic      | 0                     | 1214                  | 752   | 246                |

In the above table we compare the results of running NodeMedic-FINE flow discovery mechanism against three variants:
-   `-ObjRecon` - Object reconstruction disabled
-   `-Types` - Fuzzer only generates strings
-   `NodeMedic` - Equivalent to a replication of NodeMedic. Fuzzer is consequently disabled in this variant.

We show the number of extra and missing flows that each variant has relative to normal fuzzing in `NodeMedic-FINE`. 
We also show the total number of flows found by each variant in the same dataset.

Enabling the fuzzer increases the number of flows found from 752 to 1966, resulting in 1214 additional flows. Type-awareness in the fuzzer is responsible for finding 195 extra flows compared to a fuzzer that only generates strings. Disabling type-aware fuzzing yields 50 extra flows, 25 of which can be found by the full fuzzer with a longer timeout. The other 25 are lost due to a serialization problem when executing dynamically generated exploits with inputs of complex types.

Object reconstruction contributed to finding 74 extra flows. These were cases where the packages required inputs to be objects having a certain structure. Disabling object reconstruction also allows the fuzzer to find 37 extra flows. The limited time budget for fuzzing causes this; 26 of these 37 flows can be found
by the full fuzzer with longer timeouts while the remaining 11 cases crash after running out of memory. 
Coverage guidance that object reconstruction uses may lead the fuzzer away from generating inputs that trigger flows. 
For example, in one case the package prints an error and does not call the sink if a certain attribute is present in the user input. 
The object reconstruction mechanism will generate these attributes as coverage increases; however, the absence of those attributes is crucial for triggering the flow. 
The fuzzer found a flow in this package when object reconstruction is disabled.

We also show the number of exploited packages for each condition. Note that when the fuzzer only generates strings, it can almost reach the number of packages exploited by the default condition even after losing 145 potential flows. This is because synthesizing exploits with non-string types is harder than strings.

## High-level fuzzer result

Type- and object-structure aware fuzzing uncovers 1,966 flows; 2.6x the flows of NodeMedic. Object reconstruction is necessary to find 74 flows and generating diverse types yields 195 more flows compared to generating only strings.

## Is synthesis with the Enumerator effective for confirming ACE flows?

Once we find a flow, we try to confirm it.

| Condition      | Extra                 | Missing               | Total |
|:-------------- | ---------------------:|:---------------------:|       |
| NodeMedic-FINE | -                     | -                     | 55    |
| --Enumerator   | 0                     | 7                     | 48    |

The table above shows how NodeMedic-FINE compares against a variant that does not use the enumerator. We report the number of extra, missing, and total ACE flows for which we could successfully synthesize a working exploit (i.e. we are able to leverage the vulnerability and execute an arbitrary JavaScript statement that prints a message to the console). The enumerator is responsible for increasing the number of ACE exploits from 48 to 55 (a 15% increase). 

All 7 cases for which the enumerator contributed required a complex payload to be constructed, involving the insertion of the payload
in the right place, escaping the necessary contexts at the right time and, in some cases, an extra suffix concatenated after the prefix and our payload. 

Here we focus on ACE exploits only. In the paper we show other interesting results like the ACI exploits and detail the limitations of our tool and future work.

## High-level enumerator result

The Enumerator helped NodeMedic-FINE complete the majority of real world prefixes that we found in ACE flows, increasing the number of total confirmed ACE flows by 15%

# Conclusion

We implemented NodeMedic-FINE, an end-to-end infrastructure for automatic detection and confirmation of ACI and ACE flows in Node.js packages. Our system analysed 32,011 Node.js packages and automatically confirmed exploitable flows in 680 different packages. While our fuzzer component is significantly more effective than prior work at finding flows, the Enumerator helps us confirm exploitability of flows that were previously considered challenging.

# References

[1] François Gauthier, Behnaz Hassanshahi, and Alexander
Jordan. AFFOGATO: Runtime detection of injection
attacks for Node.js. In Companion Proceedings for the
ISSTA/ECOOP 2018 Workshops, 2018

[2] Mingqing Kang, Yichao Xu, Song Li, Rigel Gjomemo,
Jianwei Hou, V. N. Venkatakrishnan, and Yinzhi Cao.
Scaling JavaScript abstract interpretation to detect and
exploit node.js taint-style vulnerability. In IEEE Sympo-
sium on Security and Privacy, 2023.

[3] Maryna Kluban, Mohammad Mannan, and Amr Youssef.
On detecting and measuring exploitable JavaScript func-
tions in real-world applications. ACM Transactions on
Privacy and Security, 2024

[4] Song Li, Mingqing Kang, Jianwei Hou, and Yinzhi Cao.
Detecting Node.Js Prototype Pollution Vulnerabilities
via Object Lookup Analysis. 2021.

[5] Song Li, Mingqing Kang, Jianwei Hou, and Yinzhi Cao.
Mining node.js vulnerabilities via object dependence
graph and query. In 31st USENIX Security Symposium
(USENIX Security 22), 2022

[6] Cristian-Alexandru Staicu, M. Pradel, and B. Livshits.
SYNODE: Understanding and Automatically Prevent-
ing Injection Attacks on NODE.JS. In NDSS, 2018.

[7] Roberto Baldoni, Emilio Coppa, Daniele Cono D’elia,
Camil Demetrescu, and Irene Finocchi. A survey of sym-
bolic execution techniques. ACM Computing Surveys
(CSUR), 51(3):1–39, 2018.

[8] Darion Cassel, Wai Tuck Wong, and Limin Jia.
NodeMedic: End-to-end analysis of node.js vulnerabil-
ities with provenance graphs. In 2023 IEEE 8th Euro-
pean Symposium on Security and Privacy (EuroS&P),
2023.

[9] Michal Zalewski. American Fuzzy Lop
(AFL), 2024. Software available from
http://lcamtuf.coredump.cx/afl/.

[10] AFLFuzzJS. afl-fuzz-js: A JavaScript Port of the Amer-
ican Fuzzy Lop Fuzzer, Year. Software available from
URL.

[11] Valentin JM Manes, HyungSeok Han, Choongwoo Han,
Sang Kil Cha, Manuel Egele, Edward J Schwartz, and
Maverick Woo. Fuzzing: Art, science, and engineering.
arXiv preprint arXiv:1812.00140, 2018.

[12] Mingyi Zhao and Peng Liu. Empirical analysis and
modeling of black-box mutational fuzzing. In Engi-
neering Secure Software and Systems: 8th International
Symposium, ESSoS 2016, London, UK, April 6–8, 2016.
Proceedings 8, pages 173–189. Springer, 2016.
