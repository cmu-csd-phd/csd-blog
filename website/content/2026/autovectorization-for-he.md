+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "An Autovectorizing Tensor Compiler for Homomorphic Encryption"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2026-05-04

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Security", "Systems"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
# Consider these similar to keywords specified for a research paper.
tags = ["homomorphic encryption", "autovectorization", "compiler"]

[extra]
author = {name = "Edward Chen", url = "https://edwjchen.com/" }
# The committee specification is  a list of objects similar to the author.
committee = [
    {name = "Ruben Martins", url = "https://sat-group.github.io/ruben/"},
    {name = "Riad S. Wahby", url = "https://wahby.net/"},
    {name = "Harrison Grodin", url = "https://www.harrisongrodin.com/"}
]
+++

Homomorphic encryption (HE) is a powerful cryptographic technique that enables _computation on encrypted data_.
With HE, we can create privacy-preserving machine learning models that navigate privacy laws and tap into the computational power of an untrusted cloud.
However, practical adoption of HE faces two major challenges.

First, writing HE programs is exceptionally difficult.
Many lattice-based HE schemes expose a low-level vector programming model with only three homomorphic operations (add, multiply, and rotate)---essentially requiring developers to program at the level of _circuits_.
Manually translating even simple programs---let alone large language models---with this interface is tedious.
Even worse, data movement in HE is notably restrictive.
These schemes prevent direct indexing within an encrypted vector; instead, data movement is achieved through a combination of expensive homomorphic rotations, which cyclically shifts the ciphertext elements in the vector, and homomorphic multiplications with 0-1 bitmasks.
Lowering a tensor program to HE requires several complex steps:
- All input and intermediate tensors must be flattened and packed into ciphertext vectors with specific layouts.
- HE circuits must be written with respect to the ciphertext layouts.

This process is not only complex, it's brittle: any program modifications may require reassigning layouts throughout the entire computation graph.

Second, performance optimization is critical for practical deployment, as HE programs execute orders of magnitude slower than their unencrypted counterparts.
The _layout assingment_ (i.e., the layout choices assigned to each tensor operator) directly impact this performance: poor layout assignments can lead to expensive data reorganization operations between tensor computations, while optimal assignments can minimize conversion costs and unlock significant speedups.

In this blog post, we introduce Rotom, our HE compiler that automatically vectorizes tensor programs into optimized HE circuits by finding an efficient layout assignment.
We begin with a brief primer on HE, then present Rotom's high-level layout representation, layout alignment rules for generating correct HE circuits, and a new lightweight conversion optimization used in Rotom.
We conclude with a walkthrough of how Rotom finds an HE circuit for a small tensor program.
For more details about our approach and evaluation, we invite readers to see our [paper](https://eprint.iacr.org/2025/1319.pdf) and [open-source implementation](https://github.com/cmu-cryptosystems/Rotom).


## Brief Homomorphic Encryption Primer

![homomorphic encryption primer](./he.png)

HE enables secure computation on encrypted data without revealing the underlying plaintext.
In the figure above, HE allows a party \\(P_0\\) to encrypt its input \\(x\\) using a private key to get a ciphertext \\(Enc(x)\\).
A different party \\(P_1\\) applies a function \\(f\\) over the ciphertext to get \\(f(Enc(x))\\).
\\(P_1\\) cannot see the decrypted result of \\(f(x)\\) as it does not own the private key.
Since \\(P_0\\) owns the private key, \\(f(Enc(x))\\) can be decrypted by \\(P_0\\) to get \\(f(x)\\).

Lattice-based HE schemes like [BFV](#BFV), [BGV](#BGV), and [CKKS](#CKKS) have recently gained interest thanks to their efficiency.
A common trait of these schemes is their vector programming model, where \\(n\\) plaintext values are in encrypted into a single ciphertext (with \\(n\\) slots).
For example, a single plaintext vector \\(x = [x_1, x_2, . . . , x_n]\\) can be entirely encrypted into a single
ciphertext \\(Enc(x)\\).
The number of available slots within each vector is typically very large (i.e., \\(n\\) is often between 4k and 64k).
These schemes support only three HE operations: element-wise addition and multiplication, and ciphertext rotation that cyclically shifts the underlying plaintext vector.
While addition and ciphertext-plaintext multiplication are relatively low-cost in HE schemes (_≈0.1ms_), rotation and ciphertext-ciphertext multiplication are vastly more expensive (_≈10-30ms_).
Unfortunately, rotations are the sole operation that facilitates intra-ciphertext data movement.
Minimizing the number of rotations---in other words, minimizing _data movement_---is crucial to HE program performance.


## HE Compilers For Layout Assignment

> Given a tensor program, how do we assign layouts to tensors to minimize the cost of the resulting HE circuit?

We define this question as the _layout assignment problem_, an optimization problem where we explore possible layouts to find an assignment that minimizes the cost of the resulting HE program.
However, manually optimizing the layout assignment is tedious for real-world programs, which may contain thousands of possible assignments.
Thus, researchers have turned to building compilers that aim to automatically solve the layout assignment problem.
As with any optimization problem, finding an efficient solution requires balancing the tension between search speed and search quality.
Previous attempts at building autovectorizing HE compilers had one of two drawbacks.
One class of compilers ([Porcupine](#Porcupine), [Coyote](#Coyote), [Viaduct-HE](#Viaduct-HE)) used heavyweight procedures or explored vast search spaces to find highly optimized HE circuits, but complex tensor programs could take days, if not weeks, to compile due to slow search speeds.
The other class of compilers ([CHET](#CHET), [HeLayers](#HeLayers), [HECO](#HECO), [Fhelipe](#Fhelipe)) restricted the possible layouts choices, resulting in simpler searches that missed critical optimization opportunities and reduced search quality.

Our work, Rotom, aims to resolve this tension between search speed and search quality.
Rotom introduces high-level layout alignment rules to easily reason about layout compatibility, a new lightweight layout conversion operator (_ApplyRoll_) with associated optimizations, and a fast top-down enumeration search aided by pruning heuristics.


<a name="objective"></a>
## Rotom's Objective

Rotom's objective is to compile high-level tensor programs into equivalent and optimized HE circuits.
To use Rotom, users first write these programs with Rotom's PyTorch interface.
This frontend allows users to easily integrate existing machine learning models into optimized HE circuits with Rotom.
The code block below shows how we would write a simple matrix multiplication program with this interface.

```python
import numpy as np
from frontends.rotom_pytorch import torch

# Create random weights
a_data = np.random.rand(4, 4)
b_data = np.random.rand(4, 4)

# Create tensors (similar to PyTorch)
A = torch.tensor(a_data, secret=True)   # Ciphertext
B = torch.tensor(b_data, secret=False)  # Plaintext

# Matrix multiplication in PyTorch
C = torch.matmul(A, B)
```

To compile this tensor program into an HE circuit, Rotom needs to answer several questions:
- What should the input layouts of _A_ and _B_ be?
- Are the layouts for _A_ and _B_ compatible for matrix multiplication?
- What is the equivalent HE circuit for matrix multiplication given the input layouts for _A_ and _B_?
- Are there different input layouts that lead to cheaper HE circuits?

The following sections illustrates the building blocks Rotom uses to achieve this goal.


## Layout Representation
The layout representation (or "layout" for short) defines a mapping from tensor elements to ciphertext slot(s), i.e., how tensor elements are packed into a ciphertext.
Rotom adapts its layout from Viaduct-HE, using it to explore candidate layout assignments during compilation.
Below, we will briefly go over a few main ingredients used in our layout: _traversal dimensions_ and _rolls_.
For a full description, we refer the reader to Section 4 in our [paper](https://eprint.iacr.org/2025/1319.pdf).

To illustrate how to interpret a layout, we use a 4 × 4 tensor, A, whose rows and columns are indexed by axes (a.k.a. tensor dimensions) 0 and 1, respectively.

### Traversal Dimensions
A traversal dimension is defined as a sequence of tensor indices along a tensor dimension.
The notation for a traversal dimension is [**dim**:**extent**:**stride**], where **dim** denotes the tensor dimension, **extent** denotes the length of a traversal, and **stride** denotes the step-size of the traversal.
For example, **[0:4:1]** iterates through the first column of _A_, as the **dim**ension to traverse is 0, the **extent** is 4, and the **stride** is 1.
**[0:4:1]** evaluates to the indices {(0,0), (1,0), (2,0), (3,0)}; note that the indices for **dim**=1 is set to 0 as it is not defined in the layout.
Multiple traversal dimensions are evaluated as a nested loop traversal over the target tensor, where each traversal dimension is its own loop.

![column layout of A](./layout.png)

The figure above shows tensor _A_ column-packed using layout **[1:4:1][0:4:1]**.
As illustrated in the code block above, _i_ indexes **dim**=1 and _j_ indexes **dim**=0.
Both traversal dimensions have an **extent**=4 and a **stride**=1.
This layout evaluates to a column-major traversal of _A_, with indices {(0,0), (1,0), (2,0), ..., (1,3), (2,3), (3,3)}.

### Rolls

At a high-level, a roll is a layout transformation that shifts the elements of a tensor dimension by another tensor dimension.
For example, rolls can be used to transform a tensor packed in a column-major layout into a diagonal-major layout.
Intuitively, this transformation cyclically shifts each column in a tensor by its column index, (i.e., shifting
the 0th column by 0, shifting the 1st column by 1, and so on).

Formally, a roll is defined as follows.
Given a layout \\(L\\) with traversal dimensions \\([td_0, td_1, ..., td_n]\\), **Roll(i,j)** is a layout transformation that modifies the indices of a traversal dimension to be \\(td_i = (td_i + td_j)\\) % \\(td_i.extent\\).
The following example illustrates how a roll is used to achieve this column-major to diagonal-major layout transformation.
Here, **Roll(1,0)** performs a modular addition between the tensor indices of \\(td_1\\)=[0:4:1] and \\(td_0\\)=[1:4:1], modifying [0:4:1] and leaving [1:4:1] unchanged.
The resulting layout evaluates to indices {(0,0), (1,1), (2,2), (3,3), (0,1), (1,2), ..., (0,3), (1,0), (2,1), (3,2)}.

![diagonal layout of A with a roll](./roll_layout.png)


### Repeated Dimensions

Repeated dimensions _repeat_ the element of a tensor.
These traversal dimensions are represented with a \\(R\\) in the **dim** field.
The figure below illustrates how to repeat the elements from the 0th column of _A_ multiple times in a layout.

![repeating the 0th column of A](./repeated_layout.png)



## Layout Alignment

To find a correct layout assignment, we want to devise a way to lower tensor operators to equivalent HE circuits.
However, for any given tensor operation, there could be numerous starting input layouts and thus numerous different ways to construct a corresponding HE circuit.
To capture this wide search space without restricting layout choices, we need a systematic way to reason about operand layout compatibility.

Rotom addresses this challenge of operand layout compatibility by introducing layout alignment rules.
These alignment rules serve as checks to determine if two operand layouts are aligned for a given tensor operator.
Two tensor layouts are _aligned_ with respect to a tensor operation if the operation can be executed directly on the tensors _without requiring any additional data movement or layout conversion_.

For a binary tensor operation _Op_, we define an alignment constraint function that iterates through the traversal dimensions of each input operand layout and returns a boolean value: true if the layouts are aligned, otherwise false.
This constraint function also takes in a dimension alignment map, which specifies which tensor dimensions must be aligned for _Op_.
For example, two-dimensional matrix multiplication requires inner dimension alignment, i.e., **dim**=1 of the left operand must be aligned to **dim**=0 of the right operand; all other dimensions should be aligned to a repeated dimension.
Formally, two traversal dimensions at index _i_ from layout \\(L_0\\) and layout \\(L_1\\) are aligned for operation _Op_ if three conditions are met: (1) their **dim**ensions correspond according to the _Op_'s dimension alignment map, (2) they have identical extents, and (3) they have identical strides.

To give an example of layout alignment, consider a matrix multiplication program _C = A @ B_, where _A_ and _B_ are 4 × 4 tensors.
Layouts _A_=**[1:4:1][0:4:1][R:4:1]** (column-major layout where each tensor element is repeated 4 times) and _B_=**[0:4:1][R:4:1][1:4:1]** (a row-major layout where each row is repeated 4 times) are aligned for matrix multiplication.
Condition (1) is satisfied as **[1:4:1]** is aligned with **[0:4:1]**, and all other dimensions are aligned with repeated dimensions.
Conditions (2) and (3) are satisfied as all traversal dimensions have an extent of 4 and a stride of 1.
Expanding the layouts into their nested loop traversals, we can clearly see how this traversal matches that of matrix multiplication:
```python
for i in range(4):            # A:[1:4:1] = A[][i], B:[0:4:1] = B[i][]
    for j in range(4):        # A:[0:4:1] = A[j][], B:[R:4:1] = B[][]
        for k in range(4):    # A:[R:4:1] = A[][],  B:[1:4:1] = B[][k]
            C[i][j] += A[j][i] * B[i][k]
```

The figure below illustrates the aligned layouts.
With aligned layouts, the tensor operation can be directly executed without additional layout conversions.
Therefore, matrix multiplication between these two layouts can be computed by directly multiplying the ciphertexts together and summing along the inner dimension with rotations and additions.
As we can see, the elements to sum of _A_ correspond to the 0th row of _A_, and likewise the elements to sum of _B_ correspond to the 0th column of _B_.

![matmul with aligned layouts](./matmul.png)




## Using Rolls As Layout Conversions

Converting operand layouts for alignment generally involves adding repeated dimensions, compacting multiple ciphertexts (with empty slots) together, and swapping the positions of traversal dimensions.
To this end, Rotom supports 4 layout conversion operators.

1. _ApplyReplicate_ replicates values within a ciphertext by rotating and adding the same ciphertext (with empty slots) together.
2. _ApplyCompact_ performs compaction by rotating and adding different ciphertexts (with empty slots) together.
3. _ApplyPermute_ enables arbitrary layout tiling and traversal dimension reordering; misaligned values are first masked into individual ciphertexts, then compacted together.
4. _ApplyRoll_ is a new lightweight conversion introduced by Rotom that transforms a layout into a rolled layout.


![layout conversion optimization with a roll](./optimization.png)

The figure above illustrates how these conversion operators are used to swap **[1:4:1]** with the repeated dimension **[R:4:1]** in a repeated column-major layout **[R:4:1];[1:4:1][0:4:1]**.
(Note that \\(;\\) represents a segmentation operator, which splits the layout in multiple ciphertexts. In this case, four ciphertexts each of size n=16.)

Part 1 shows the conversion using _ApplyPermute_.
1. Each column (color) is first masked into its own ciphertext.
2. Then each column is replicated within the ciphertext.

The conversion results in 4 multiplications, 8 rotations, and 8 additions, as the _Replicate_ step requires multiple rotations and additions per ciphertext.

Part 2 shows the conversion using _ApplyRoll_.
1. Each column is rotated internally within the ciphertext, which requires 1 mask, 1 sub/add, and 2 rotations to get each rotated partition.
2. Then, the partitions are compacted together.

This conversion uses 3 multiplications, 6 rotations, and 6 additions.
Crucially, _ApplyRoll_ avoids the _Replicate_ step used by _ApplyPermute_, which saves on rotations.
Furthermore, _ApplyRoll_ can be optimized even further to **only use 3 rotations** in this example.
Unlike prior work, Rotom uses this _ApplyRoll_ operator to cheaply perform layout conversions and find additional optimization opportunities.

<!-- Our key insight in using _ApplyRoll_ as a layout conversion operator is that rolling a traversal dimension by a repeated dimension enables Rotom to swap the two traversal dimensions.
Recall that a roll modifies the tensor indices of a traversal dimension by applying a modular addition
with another traversal dimension’s indices.
The intuition behind this conversion is that modular addition is _commutative_, thus swapping the order of both the traversal dimensions does not change the resulting tensor indices.
This property only holds because a repeated dimension contributes the same constant offset to every tensor index during the modular addition.
For example, **Roll(1,0)[R:4:1][0:4:1][1:4:1]** is equivalent to **Roll(0,1)[0:4:1][R:4:1][1:4:1]**, as the rolls in both layouts modify the tensor indices of **[0:4:1]** by adding the tensor indices of **[R:4:1]**.
The code block below illustrates how the two rolled layouts are equivalent.
```python
# Layout: Roll(1,0)[R:4:1][0:4:1][1:4:1]
for i in range(4):            # A:[R:4:1]   = A[][]
    for j in range(4):        # A:Roll(1,0) = A[(j+i)%4][]
        for k in range(4):    # A:[1:4:1]   = A[][k]
            V[16*i+4*j+k] = A[(j+i)%4][k]

# Layout: Roll(0,1)[0:4:1][R:4:1][1:4:1]
for i in range(4):            # A:Roll(0,1) = A[(i+j)%4][]
    for j in range(4):        # A:[R:4:1]   = A[][]
        for k in range(4):    # A:[1:4:1]   = A[][k]
            V[16*i+4*j+k] = A[(i+j)%4][k]
```
Rotom uses this insight to proactively use ApplyRoll when swapping a traversal dimension with a repeated dimension.
 -->
<!--
The figure below illustrates how _ApplyPermute_ and _ApplyRoll_ can be used
While both _ApplyPermute_ and _ApplyRoll_ can swap dimensions, these two operators lead to very different conversion costs.  -->


# Putting It All Together

Recall the matrix multiplication example from [Rotom's Objective](#objective), where _A_ and _B_ are both input 4 × 4 tensors.
Rotom's layout assignment algorithm works as follows.
First, Rotom parses the input tensor program into its tensor intermediate representation (IR).
Next, Rotom seeds each input tensor with a set of compact layouts, e.g., variations of row, column, and tiled layouts.
Rotom processes each tensor operator in topological order, generating equivalent HE circuits based on the available layouts from predecessor operations, thereby maintaining layout compatibility across the entire computation graph.


![Illustrated plaintext matrix multiplication program](./pt.png)

For example, let _A_ and _B_ be seeded with row and column layouts respectively.
This means each input tensor has the candidate layouts **[0:4:1][1:4:1]** (row) and **[1:4:1][0:4:1]** (column) respectively.
To find an equivalent HE circuit for _C = A @ B_, Rotom tries all pairwise combinations from its operand layout candidate pool.
Consider if Rotom chooses _A_=**[1:4:1][0:4:1]**.


The figure below details the HE circuit generated by Rotom for this matrix multiplication program.

1. Rotom uses _ApplyReplication_ on _A_ to add a repeated dimension necessary for matrix multiplication, transforming _A_'s layout from **[1:4:1][0:4:1]** to **[R:4:1];[1:4:1][0:4:1]**.
2. Rotom optimizes the layout by swapping **[1:4:1]** with **[R:4:1]** using an _ApplyRoll_, creating the layout **Roll(0,1)[1:4:1];[R:4:1][0:4:1]**.
   - Critically, this layout conversion is cheaper than using _ApplyPermute_, which is used by prior systems.
   - In addition, Rotom avoids expensive intra-ciphertext rotations by summing across ciphertexts rather than within ciphertexts.
3. Since _B_ is a plaintext, it can be freely repacked at no additional cost, as _B_ can directly be encoded into an aligned layout. Using its alignment rules, Rotom finds the aligned layout **Roll(0,1)[0:4:1];[1:4:1][0:4:1]**.
4. After aligning the operand layouts, Rotom can directly execute matrix multiplication, producing the output layout _C_=**[1:4:1][0:4:1]**.


![Illustrated HE circuit for matrix multiplication](./opt.png)


# Evaluation

Our paper provides detailed coverage of additional roll-based optimizations and search pruning heuristics that help to achieve scalable layout assignment times.
We also present a comprehensive evaluation comparing Rotom's performance against existing HE compilers across 6 different tensor workloads, demonstrating substantial improvements in both compilation speed and HE program execution.

![Compile time evaluation](./compile.png)
*Compilation time comparison in Log-Scale. t-out indicates the benchmark did not compile within 24hrs.*

The figure above compares compilation time against Fhelipe and Viaduct-HE in log-scale.
Rotom compiles most benchmarks _in seconds_ and all benchmarks within 5 minutes.
Although Fhelipe also achieves fast compilation, it restricts the possible layout choices, sacrificing solution quality for compilation speed.
Viaduct-HE, on the other hand, times out on larger benchmarks due to its expensive array materialization step.
This step explicitly constructs the full array of slot indices (where n = 4k to 64k) for each candidate layout to derive layout conversions.


![Execution time evaluation](./runtime.png)
*Performance in Log-Scale on [OpenFHE](#OpenFHE). t-out indicates the benchmark did not compile within 24hrs.*

The figure above compares execution time against Fhelipe and Viaduct-HE in log-scale.
Rotom either matches or outperforms both baselines across all benchmarks, with speedups of up to 34× over Viaduct-HE adn 80× over Fhelipe.
These gains largely stem from Rotom's _ApplyRoll_ operator, which enables complex layouts like diagonalization and baby-step giant-step optimizations that greatly reduce the number of HE rotations -- optimizations that Fhelipe and Viaduct-HE lack.


For complete technical details on these optimizations and experimental results, we encourage readers to see our [paper](https://eprint.iacr.org/2025/1319.pdf).


# Conclusion

This blog post is based on joint work with [Fraser Brown](https://mlfbrown.com/) and [Wenting Zheng](https://wzheng.github.io/).
Rotom addresses a key barrier to practical HE by automatically finding efficient layout assignments for tensor programs.
By automating layout assignment, this work makes HE more accessible for practical applications.

Future work will focus on discovering additional novel abstractions, similar to _ApplyRoll_, that can enhance layout assignment strategies and unlock new optimization opportunities.
Tangential directions include extending Rotom with noise management operations for FHE program optimization and supporting end-to-end large language models in this framework.
There are already some exciting efforts to incorporate Rotom into [HEIR](https://heir.dev/), a production-ready compiler toolchain for FHE.

---
## Bibliography

- <a name="BFV"></a> Zvika Brakerski, Craig Gentry, and Vinod Vaikuntanathan. (leveled) fully homomorphic encryption without bootstrapping. ACM Transactions on Computation Theory (TOCT), 6(3):1–36, 2014. <https://dl.acm.org/doi/pdf/10.1145/2633600>
- <a name="CKKS"></a> Jung Hee Cheon, Andrey Kim, Miran Kim, and Yongsoo
Song. Homomorphic encryption for arithmetic of approximate numbers. In International conference on the
theory and application of cryptology and information
security, pages 409–437. Springer, 2017. <https://link.springer.com/chapter/10.1007/978-3-319-70694-8_15>
- <a name="BGV"></a> Junfeng Fan and Frederik Vercauteren. Somewhat practical fully homomorphic encryption. Cryptology ePrint Archive, 2012. <https://eprint.iacr.org/2012/144>
- <a name="Fhelipe"></a> Aleksandar Krastev, Nikola Samardzic, Simon Langowski, Srinivas Devadas, and Daniel Sanchez. A tensor compiler with automatic data packing for simple and efficient fully homomorphic encryption. Proceedings of the ACM on Programming Languages, 8(PLDI):126–150, 2024. <https://dl.acm.org/doi/full/10.1145/3656382>
- <a name="Viaduct-HE"></a> Rolph Recto and Andrew C Myers. A compiler from array programs to vectorized homomorphic encryption.arXiv preprint arXiv:2311.06142, 2023. <https://arxiv.org/abs/2311.06142>
- <a name="CHET"></a> Roshan Dathathri, Olli Saarikivi, Hao Chen, Kim Laine, Kristin Lauter, Saeed Maleki, Madanlal Musuvathi, and Todd Mytkowicz. Chet: an optimizing compiler for fully-homomorphic neural-network inferencing. In Proceedings of the 40th ACM SIGPLAN conference on programming language design and implementation, pages 142–156, 2019. <https://dl.acm.org/doi/pdf/10.1145/3314221.3314628>
- <a name="HECO"></a> Alexander Viand, Patrick Jattke, Miro Haller, and Anwar Hithnawi. {HECO}: Fully homomorphic encryption compiler. In 32nd USENIX Security Symposium (USENIX Security 23), pages 4715–4732, 2023. <https://www.usenix.org/conference/usenixsecurity23/presentation/viand>
- <a name="HeLayers"></a> Ehud Aharoni, Allon Adir, Moran Baruch, Nir Drucker, Gilad Ezov, Ariel Farkash, Lev Greenberg, Ramy Masalha, Guy Moshkowich, Dov Murik, et al. Helayers: A tile tensors framework for large neural networks on encrypted data. arXiv preprint arXiv:2011.01805, 2020. <https://arxiv.org/abs/2011.01805>
- <a name="Porcupine"></a> Meghan Cowan, Deeksha Dangwal, Armin Alaghi, Caroline Trippel, Vincent T Lee, and Brandon Reagen. Porcupine: A synthesizing compiler for vectorized homomorphic encryption. In PLDI, 2021. <https://dl.acm.org/doi/pdf/10.1145/3453483.3454050>
- <a name="Coyote"></a> Raghav Malik, Kabir Sheth, and Milind Kulkarni. Coyote: A compiler for vectorizing encrypted arithmetic circuits. In Proceedings of the 28th ACM Internationa Conference on Architectural Support for Programming Languages and Operating Systems, Volume 3, pages 118–133, 2023. <https://dl.acm.org/doi/pdf/10.1145/3582016.3582057>
- <a name="OpenFHE"></a> Ahmad Al Badawi, Jack Bates, Flavio Bergamaschi, David Bruce Cousins, Saroja Erabelli, Nicholas Genise, Shai Halevi, Hamish Hunt, Andrey Kim, Yongwoo Lee, et al. Openfhe: Open-source fully homomorphic encryption library. In Proceedings of the 10th Workshop on Encrypted Computing & Applied Homomorphic Cryptography, pages 53–63, 2022. <https://dl.acm.org/doi/abs/10.1145/3560827.3563379>
