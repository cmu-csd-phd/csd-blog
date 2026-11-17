+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "Solving Linear Systems with Modular Arithmetic"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2026-11-17
# Keep this post out of the published site until review is complete.
draft = false

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Theory"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
# Consider these similar to keywords specified for a research paper.
tags = ["linear systems", "modular arithmetic", "finite fields", "p-adic lifting", "space complexity"]

[extra]
author = {name = "Junzhao Yang", url = "https://fizzydavid.github.io" }
# The committee specification is  a list of objects similar to the author.
committee = [
    {name = "Yang P. Liu", url = "https://yangpliu.github.io/index.html"},
    {name = "Weina Wang", url = "https://www.cs.cmu.edu/~weinaw/"},
    {name = "Yixuan (Even) Xu", url = "https://yixuanevenxu.github.io/"}
]
+++

# Why study linear systems?

Solving linear systems is a fundamental problem in mathematics and computer science, with applications throughout science and engineering. It is a basic tool in machine learning, optimization, scientific simulation, computational number theory, and more.

In linear regression, we are given a data matrix \\( B\in\mathbb R^{N\times d} \\) and a vector \\( y\in\mathbb R^N \\). For simplicity, assume that the columns of \\( B \\) are linearly independent. We choose \\( x\in\mathbb R^d \\) to minimize the squared error \\( \lVert Bx-y\rVert_2^2 \\). Setting the gradient of this objective to zero gives the linear system \\( B^\top Bx=B^\top y \\), known as the normal equations. Therefore, solving a linear regression problem reduces to solving a linear system.

Linear systems also appear in computational number theory. Algorithms for factoring large integers and computing discrete logarithms, such as those in the [CADO-NFS project](https://cado-nfs.gitlabpages.inria.fr/), collect many arithmetic relations. These relations lead to large, sparse linear systems over finite fields, where arithmetic is performed modulo a prime.

In this post, we focus on square, invertible systems of the form

$$
Ax=b,
$$

where \\( A \\) is an invertible \\( n\times n \\) matrix, \\( b \\) is a given \\( n \\)-dimensional vector, and \\( x \\) is unknown. We write \\( m \\) for the number of nonzero entries of \\( A \\). A dense matrix has \\( m=\Theta(n^2) \\), while a very sparse matrix has \\( m=O(n) \\) nonzeros.

Given the many applications of linear systems, understanding the time and space needed to solve them is an important algorithmic problem. We want to understand how these costs depend on the dimension \\( n \\) and the number of nonzeros \\( m \\).

You may already know that a dense linear system can be solved in \\( n^{\omega+o(1)} \\) arithmetic operations, where \\( \omega \\) is the matrix multiplication exponent. This bound counts each addition, subtraction, multiplication, or division as a single operation, regardless of how many bits the numbers contain. The actual time needed to perform these operations, and the space needed to store intermediate results, depend on the bit lengths of these numbers.

Returning to our two examples, linear regression leads to a numerical problem over the reals, where we usually seek an approximate solution and must control rounding errors. This is the **numerical setting**. The number-theoretic applications lead to systems over finite fields, where arithmetic is exact modulo a prime. This is the **finite-field setting**. This blog explores the connection between these two settings through the following question:

**Can methods from the finite-field setting help us solve a linear system over the reals in the numerical setting?**

This post presents three algorithms that answer this question affirmatively:

1. Dixon's algorithm \[[Dix82](https://doi.org/10.1007/BF01459082)\], which recovers exact rational solutions by lifting modular solutions.
2. The linear-space algorithm of Liu, Nguyen, and Yang \[[LNY26](https://arxiv.org/abs/2507.02433)\], which solves numerical systems using linear working space.
3. Kelner's algorithm \[[Kel26](https://arxiv.org/abs/2609.38101)\], which reduces the running time for sparse numerical systems.

# Two settings: Finite-field vs Numerical

## The finite-field setting

> **Definition 1 (Finite-field linear system solving).** Given an invertible matrix \\( A\in\mathbb F\_p^{n\times n} \\) and a vector \\( b\in\mathbb F\_p^n \\), where \\( p \\) is prime, compute \\( x\in\mathbb F\_p^n \\) such that \\( Ax=b \\) over \\( \mathbb F\_p \\).

<p></p>

The field \\( \mathbb F\_p \\) consists of the residues \\( 0,1,\ldots,p-1 \\), with addition and multiplication modulo \\( p \\). Every nonzero residue has an inverse. We will use primes whose binary length is \\( O(\log n) \\). Each field element then fits in one machine word.

**Example (finite field).** Let \\( p=5 \\) and consider

$$
A=\begin{bmatrix}2&1\\\\1&2\end{bmatrix},
\qquad
b=\begin{bmatrix}1\\\\0\end{bmatrix}.
$$

The solution over \\( \mathbb F\_5 \\) is \\( x=[4,3]^\top \\), since \\( Ax=[11,10]^\top\equiv[1,0]^\top=b\pmod5 \\).

<!-- It is important that the modulus is prime. Arithmetic modulo \\( p^k \\), or modulo a power of two, is generally arithmetic in a ring rather than a field. We will use these larger moduli during lifting, while the modular solver in this definition works over a field. -->

## The numerical setting

> **Definition 2 (Numerical linear system solving).** Given an invertible integer matrix \\( A\in\mathbb Z^{n\times n} \\) and an integer vector \\( b\in\mathbb Z^n \\), compute an approximation \\( \widehat x \\) to the exact solution \\( x^\star=A^{-1}b \\) under a specified approximation guarantee.

<p></p>

**Example (numerical).** For the same \\( A \\) and \\( b \\), the exact solution is \\( x^\star=[2/3,-1/3]^\top \\). A numerical approximation is \\( \widehat x=[0.667,-0.333]^\top \\), whose error is \\( \widehat x-x^\star=[1/3000,1/3000]^\top \\). Here we measure how close the answer is to the exact solution.

**Remark (integer input).** We assume integer input to simplify the presentation. Rational inputs can be converted exactly by multiplying \\( A \\) and \\( b \\) by the least common multiple of their denominators. For numerical approximation, we can instead scale and round the input to integers, using enough precision to control the error in the solution.

There are several ways to measure approximation. We will use the following definitions for \\( 0<\epsilon<1 \\):

<a id="approximation-guarantees"></a>

> **Definition 3 (Approximation guarantees).**
>
> - A **normwise approximation guarantee** requires
>
>   $$
>   \\|\widehat x-x^\star\\|\_2\leq\epsilon\\|x^\star\\|\_2.
>   $$
>
> - An **entrywise approximation guarantee** requires
>
>   $$
>   |\widehat x\_j-x^\star\_j|\leq\epsilon|x^\star\_j|
>   \qquad\text{for every }j.
>   $$
>
>   Since \\( 0<\epsilon<1 \\), this preserves the sign of every nonzero coordinate. If \\( x^\star\_j=0 \\), the approximation must also be zero.

<p></p>

A normwise guarantee measures error in the solution as a whole. Entrywise accuracy implies normwise accuracy with the same \\( \epsilon \\). Under a normwise guarantee, small coordinates may be poorly approximated. An entrywise guarantee requires every coordinate to be close to its true value.

In the numerical setting, another important input parameter is the condition number, which helps describe how difficult it is to compute an accurate solution. It measures how sensitive the solution can be to changes in the input. In the Euclidean norm, define

$$
\kappa=\\|A\\|\_2\\|A^{-1}\\|\_2
      =\frac{\sigma\_{\max}(A)}{\sigma\_{\min}(A)}.
$$

The singular values describe how much the matrix stretches vectors in different directions. If one direction is compressed much more than another, applying the inverse can greatly amplify a small error. For a symmetric positive-definite matrix, the condition number is the ratio of the largest to the smallest eigenvalue.

For example, let

$$
A=\begin{bmatrix}1&0\\\\0&\delta\end{bmatrix},
\qquad
b=\begin{bmatrix}1\\\\0\end{bmatrix},
\qquad 0<\delta<1.
$$

The exact solution is \\( x^\star=[1,0]^\top \\). Replacing \\( b \\) with \\( \widetilde b=[1,\delta]^\top \\) changes the solution to \\( \widetilde x=[1,1]^\top \\). Thus a change of \\( \delta \\) in the right-hand side, measured in the Euclidean norm, causes a change of \\( 1 \\) in the solution. Here \\( \kappa=1/\delta \\). In general, when \\( A \\) is fixed,

$$
\frac{\\|\widetilde x-x^\star\\|\_2}{\\|x^\star\\|\_2}
\leq
\kappa\frac{\\|\widetilde b-b\\|\_2}{\\|b\\|\_2},
$$

where \\( A\widetilde x=\widetilde b \\) and \\( b\neq0 \\). A large condition number can therefore require more precision to keep the solution error small.

A common setting is to study *polynomially conditioned systems*, where \\( \kappa\leq n^C \\) for some constant \\( C \\).

# Existing algorithms and complexity bounds

We focus on running time and working space. **Running time** is measured in bit operations, rather than arithmetic operations. This distinction is especially important in the numerical setting, where rounding errors can accumulate and the number of bits needed per number may grow with \\( n \\). **Working space** is measured in bits and counts the additional memory required by an algorithm, assuming read-only access to the input. A space-efficient algorithm may use only \\( \widetilde O(n) \\) bits of working space by maintaining a few vectors, even the input matrix itself takes \\( O(n^2) \\) space. 

## Standard approaches

Gaussian elimination is the standard textbook method. In the numerical setting, complete pivoting controls intermediate growth by choosing the largest entry in absolute value from the remaining submatrix. Its error analysis implies that \\( O(\log^2 n+\log(\kappa/\epsilon)) \\) bits per number suffice to achieve normwise error \\( \epsilon \\) \[[Hig11](https://eprints.maths.manchester.ac.uk/1579/1/lu5a.pdf)\]. In some cases, exploiting properties of the system can lead to better bounds.

Iterative methods improve an approximate solution through repeated matrix-vector products. A standard example is the conjugate gradient method (CG), which applies to symmetric positive-definite matrices \[[She94](https://www.cs.cmu.edu/~quake-papers/painless-conjugate-gradient.pdf)\]. Each iteration uses \\( O(m) \\) arithmetic operations, and the method stores only \\( O(n) \\) numbers.

In exact arithmetic, CG can achieve the normwise guarantee in [Definition 3](#approximation-guarantees) within \\( O(\sqrt{\kappa}\log(\kappa/\epsilon)) \\) iterations. It also reaches the exact solution within \\( n \\) iterations. Combining these bounds gives a total cost of

$$
O\left(m\min\left\\{n,\sqrt{\kappa}\log\frac{\kappa}{\epsilon}\right\\}\right)
$$

arithmetic operations. A small condition number can therefore make CG converge quickly. These bounds assume exact arithmetic: rounding errors can destroy the \\( n \\)-step termination guarantee \[[Kel26](https://arxiv.org/abs/2609.38101)\]. To converge within \\( O(n) \\) iterations, CG requires storing \\( \widetilde O(n) \\) bits per number to control the error, at a cost of \\( \widetilde O(mn^2) \\) bit operations and \\( \widetilde O(n^2) \\) bits of working space \[[MMS18](https://arxiv.org/abs/1708.07788)\].

An alternative implementation of CG uses fewer bits to store a number but has worse convergence bound that may have polynomial dependendence on the condition number. CG with only \\( O(\log n) \\) bits per number converges in \\( \widetilde O(\sqrt{\kappa}) \\) iterations. It runs in \\( \widetilde O(m\sqrt{\kappa}) \\) bit operations and uses \\( O(n\log n) \\) bits of working space \[[MMS18](https://arxiv.org/abs/1708.07788)\]. This implementation may take more than \\( n \\) iterations.

<figure id="standard-approaches-table">

| Method | Bit operations | Working space (bits) |
|:---|:---|:---|
| Gaussian elimination with complete pivoting | \\( \widetilde O(n^3) \\) | \\( \widetilde O(n^2) \\) |
| CG with \\( \widetilde O(n) \\)-bit precision | \\( \widetilde O(mn^2) \\) | \\( \widetilde O(n^2) \\) |
| CG with \\( O(\log n) \\)-bit precision \[[MMS18](https://arxiv.org/abs/1708.07788)\] | \\( \widetilde O(m\sqrt{\kappa}) \\) | \\( O(n\log n) \\) |

<figcaption>
<b>Table 1.</b> Running time and space of standard methods. For numerical linear system solving, assume polynomially bounded integer inputs, polynomially bounded \( \kappa \), and inverse-polynomial normwise error. The notation \( \widetilde O \) suppresses logarithmic factors. Working space excludes the read-only input and the output.
</figcaption>
</figure>

## Finite-field methods

The classic Gaussian elimination algorithm uses \\( O(n^3) \\) field operations and stores \\( O(n^2) \\) field elements. However, faster algorithms are available for dense matrices via fast matrix multiplication and for sparse matrices via Wiedemann's algorithm.

Over finite fields, Wiedemann's randomized algorithm \[[Wie86](https://doi.org/10.1109/TIT.1986.1057137)\] solves a system exactly using \\( O(n) \\) black-box matrix-vector products. It accesses \\( A \\) only through an operation that returns \\( Av \\) for a given vector \\( v \\). Each product takes \\( O(m) \\) field operations, and the algorithm takes \\( \widetilde O(nm) \\) field operations in total while storing only \\( O(n) \\) field elements. We will rely on this algorithm later, but treat it as a black box. We remark that finite-field variants of CG can achieve similar time and space bounds \[[EK97](https://cspages.ucalgary.ca/~eberly/Research/Papers/lanczos_with_proofs.pdf)\], but we focus only on Wiedemann's algorithm in this post.

<figure id="finite-field-baselines-table">

| Matrix regime | Algorithm | Field operations | Working space (field elements) |
|:---|:---|:---|:---|
| Dense | Gaussian elimination | \\( O(n^3) \\) | \\( O(n^2) \\) |
| Dense | Fast matrix multiplication | \\( n^{\omega+o(1)} \\) | \\( O(n^2) \\) |
| Very sparse | Wiedemann \[[Wie86](https://doi.org/10.1109/TIT.1986.1057137)\] | \\( \widetilde O(nm)=\widetilde O(n^2) \\) | \\( O(n) \\) |

<figcaption>
<b>Table 2.</b> Time and space for finite-field linear system solving. Dense matrices have \( m=\Theta(n^2) \) nonzero entries, and very sparse matrices have \( m=\widetilde O(n) \). Time counts exact field operations, and working space counts field elements, excluding the read-only input and the output. The prime has \( O(\log n) \) bits, so each field operation costs polylogarithmically many bit operations.
</figcaption>
</figure>

## Numerical baselines

Beyond standard approaches, numerical solvers can achieve better worst-case running times. Stable algorithms based on fast matrix multiplication give faster dense solvers \[[DDH07](https://arxiv.org/abs/math/0612264)\]. Algorithms designed for sparse matrices can improve on the dense bound \[[PV21](https://arxiv.org/abs/2007.10254)\].

For these numerical bounds, \\( \omega \\) refers to matrix multiplication over the reals. Table 3 substitutes OpenAI's recent bound \\( \omega(\mathbb C)\leq9/4 \\) \[[OAI26](https://github.com/openai/math/blob/main/lean/docs/107.md)\] into the running times.

<figure id="numerical-baselines-table">

| Matrix regime | Algorithm | Bit operations | Working space (bits) |
|:---|:---|:---|:---|
| Dense | Stable fast linear algebra \[[DDH07](https://arxiv.org/abs/math/0612264)\] | \\( O(n^{2.25+\eta}) \\) | \\( \widetilde O(n^2) \\) |
| Very sparse | Peng–Vempala \[[PV21](https://arxiv.org/abs/2007.10254)\] | \\( O(n^{29/13+\eta}) \\) | \\( \widetilde O(n^2) \\) |
| Very sparse | Nie's refinement \[[Nie22](https://arxiv.org/abs/2111.05553)\] | \\( O(n^{2.2+\eta}) \\) | \\( \widetilde O(n^2) \\) |

<figcaption>
<b>Table 3.</b> Time and space for numerical linear system solving, for any fixed \( \eta>0 \). The time exponents before substitution are \( \omega \), \( (5\omega-4)/(\omega+1) \), and \( (3\omega-4)/(\omega-1) \), respectively; \( 29/13\approx2.23077 \). The arbitrarily small \( \eta \) accounts for exponent slack and absorbs logarithmic factors. Time is measured in bit operations and working space in bits, excluding the read-only input and the output. Dense matrices have \( m=\Theta(n^2) \), and very sparse matrices have \( m=\widetilde O(n) \). Assume polynomially bounded integer entries, a known polynomial bound on \( \kappa \), and a target normwise error \( \epsilon=1/\operatorname{poly}(n) \).
 <!-- The sparse space bounds follow from using implicit Krylov matrices and structured representations of their solvers. -->
</figcaption>
</figure>

## Time and space in this post

The three algorithms in this post bring finite-field methods into numerical linear system solving through modular arithmetic, each with a different advantage.

Dixon's algorithm recovers an **exact rational solution**. The algorithm of Liu, Nguyen, and Yang uses only **\\( O(n\log n) \\) bits of working space** while providing an **entrywise approximation guarantee**. For very sparse, polynomially conditioned systems, Kelner's algorithm uses only **\\( \widetilde O(n^2) \\) bit operations**. Table 4 compares their time, space, and accuracy guarantees.

<figure id="algorithms-in-this-post-table">

| Algorithm | Bit operations | Working space (bits) | Approximation guarantee |
|:---|:---|:---|:---|
| Dixon with Wiedemann \[[Dix82](https://doi.org/10.1007/BF01459082), [Wie86](https://doi.org/10.1109/TIT.1986.1057137)\] | \\( \widetilde O(n^3) \\) | \\( O(n^2\log n) \\) | **Exact** |
| Liu–Nguyen–Yang \[[LNY26](https://arxiv.org/abs/2507.02433)\] | \\( \widetilde O(n^3) \\) | \\( \boldsymbol{O(n\log n)} \\) | **Entrywise** |
| Kelner \[[Kel26](https://arxiv.org/abs/2609.38101)\] | \\( \boldsymbol{\widetilde O(n^2)} \\) | \\( \widetilde O(n^2) \\) | Normwise |

<figcaption>
<b>Table 4.</b> Time, space, and accuracy for the three algorithms in this post. Assume very sparse matrices with \( m=\widetilde O(n) \), polynomially bounded integer entries, and inverse-polynomial error for the approximate solvers. Kelner's row also assumes a known polynomial bound on \( \kappa \); Dixon and Liu–Nguyen–Yang require no condition-number bound. The Dixon row uses Wiedemann for each modular solve and stores the full lifted vector. Working space excludes the read-only input and the output.
</figcaption>
</figure>

All three algorithms use exact modular computations to recover rational solutions or numerical approximations. We begin with Dixon's lifting method, using Wiedemann's finite-field solver as a black box.

# Dixon's algorithm: p-adic lifting

The *p-adic viewpoint* describes a number through its residues modulo increasing powers of a prime \\( p \\). A residue modulo \\( p^k \\) can be written in base \\( p \\) as

$$
a\_0+a\_1p+\cdots+a\_{k-1}p^{k-1},
$$

where each \\( a\_i \\) is one of \\( 0,1,\ldots,p-1 \\), called a *base-\\( p \\) digit*. Knowing a number modulo \\( p^k \\) means knowing its first \\( k \\) digits, starting from the lowest power of \\( p \\). Extending this information to modulo \\( p^{k+1} \\) reveals the next digit.

Dixon's algorithm \[[Dix82](https://doi.org/10.1007/BF01459082)\] applies this idea to each coordinate of the solution. It starts with a solution modulo a suitable small prime \\( p \\), then extends it to solutions modulo \\( p^2,p^3,\ldots \\). This process is called *p-adic lifting*. Once \\( p^k \\) is large enough, the modular solution contains enough information to recover the exact rational solution through *rational reconstruction*.

The advantage of using powers of a small prime, rather than one huge prime, is that each lifting step only requires solving a system modulo \\( p \\). Each intermediate field element is represented by a single base-\\( p \\) digit in \\( 0,\ldots,p-1 \\), even as we accumulate information modulo a growing power of \\( p \\).

Suppose we already know the solution modulo \\( p^k \\). Write

$$
x\equiv zp^k+y\pmod{p^{k+1}},
$$

where \\( y \\) and \\( z \\) are integer vectors. Each coordinate of \\( y \\) lies in \\( 0,\ldots,p^k-1 \\) and contains the known first \\( k \\) base-\\( p \\) digits. Each coordinate of \\( z \\) lies in \\( 0,\ldots,p-1 \\) and is the next unknown digit. Substituting into \\( Ax=b \\) and dividing the resulting congruence by \\( p^k \\) gives

$$
Az\equiv\frac{b-Ay}{p^k}\pmod p.
$$

The right-hand side is an integer vector because \\( Ay\equiv b\pmod{p^k} \\). To determine \\( x \\) modulo \\( p^{k+1} \\), we only need to find \\( z \\). We can do this by solving the new system **modulo \\( p \\)**, using Wiedemann's algorithm.

Now denote the known part \\( y \\) by \\( s\_k \\) and the \\( k \\)-th p-adic digit of \\( x \\), namely \\( z \\), by \\( x\_k \\). This gives the lifting recurrence

$$
Ax\_k\equiv \frac{b-As\_k}{p^k}\pmod p,
\qquad
s\_{k+1}=s\_k+p^k x\_k.
$$

The updated vector \\( s\_{k+1} \\) solves the original system modulo \\( p^{k+1} \\). Each finite-field solve therefore adds one digit of modular precision.

Computing \\( b-As\_k \\) from scratch at every step would involve the growing entries of \\( s\_k \\). To implement lifting efficiently, we maintain the scaled residual

$$
r\_k=\frac{b-As\_k}{p^k}.
$$

The next digit satisfies \\( Ax\_k\equiv r\_k\pmod p \\). Once it is known, the identity \\( s\_{k+1}=s\_k+p^k x\_k \\) gives

$$
r\_{k+1}
=\frac{b-As\_{k+1}}{p^{k+1}}
=\frac{r\_k-Ax\_k}{p}.
$$

The division is exact because \\( Ax\_k\equiv r\_k\pmod p \\). Thus updating the residual only requires multiplying \\( A \\) by the digit vector \\( x\_k \\), subtracting, and dividing by \\( p \\). For polynomially bounded integer inputs, the residual entries remain polynomially bounded and need only \\( O(\log n) \\) bits each.

We use *rational reconstruction*, an efficient procedure based on the extended Euclidean algorithm, as a black box. Suppose an unknown reduced fraction \\( a/b \\) satisfies \\( |a|\leq H \\) and \\( 1\leq b\leq H \\). Given its residue \\( ab^{-1}\bmod M \\), the black box recovers \\( a \\) and \\( b \\) whenever \\( M>2H^2 \\), provided \\( b \\) is invertible modulo \\( M \\).

After \\( T \\) iterations of p-adic lifting, we know

$$
s\_T=x\_0+x\_1p+x\_2p^2+\cdots+x\_{T-1}p^{T-1}
\equiv x\pmod{p^T}.
$$

Once \\( p^T>2H^2 \\), we apply rational reconstruction to each coordinate of \\( s\_T \\) to recover the exact rational solution. For polynomially bounded integer inputs, Cramer's rule and determinant bounds give \\( \log H=O(n\log n) \\), so \\( T=O(n) \\) iterations suffice with a polynomial-size prime.

Using Wiedemann's solver at each of the \\( O(n) \\) lifting steps gives a total running time of \\( \widetilde O(n^2m) \\) bit operations, or \\( \widetilde O(n^3) \\) for very sparse systems. Therefore, Dixon's algorithm uses finite-field methods to recover the exact rational solution \\( x \in \mathbb Q^n \\) to \\( Ax=b \\) in the numerical setting. No approximation or rounding error is incurred.

<!-- Even when we use Wiedemann's solver for each correction, storing the full lifted vector costs \\( O(n^2\log n) \\) bits in the worst case. Can we use the same lifting idea while keeping only \\( O(n\log n) \\) bits of working space? -->

# Solving numerical linear systems in linear space

In *Numerical Linear Algebra in Linear Space* \[[LNY26](https://arxiv.org/abs/2507.02433)\], presented at SODA 2026, Yiping Liu, Hoai-An Nguyen, and I study space-efficient linear system solvers. Recall that the working space is counted separately from the read-only input and the output. The algorithm can revisit the input, but cannot use the output as scratch space.

For this discussion, assume that the integer entries of \\( A \\) and \\( b \\) are polynomially bounded in \\( n \\), and that \\( \epsilon \\) is inverse-polynomial in \\( n \\). Recall that Wiedemann's algorithm uses linear working space in the finite-field setting. Can we also achieve linear working space in the numerical setting, and how fast can such a solver be?

Our algorithm runs in \\( \widetilde O(n^2m) \\) bit operations and uses \\( O(n\log n) \\) bits of working space, achieving an entrywise \\( \epsilon \\)-approximation guarantee with high probability. Our approach builds on Dixon’s p-adic lifting. Our new idea is to use the determinant to make the solution integral, allowing us to approximate the coordinates using small space in a streaming setting we'll define later. Our main technical contribution is a variant of the lifting procedure that stores a small carry vector instead of the large residual.

## The first attempt: plain p-adic lifting

A natural first attempt is to use Dixon's algorithm directly. After \\( T=O(n) \\) lifting steps, rational reconstruction recovers the solution from \\( s\_T=x\bmod p^T \\). However, each coordinate of \\( s\_T \\) may need \\( O(n\log n) \\) bits, so storing the full vector would already cost quadratic space.

To use linear working space, we accumulate the lifted digits for only one output coordinate, while still maintaining the short residual and current digit vectors. After rational reconstruction, we output that coordinate and repeat the lifting process for the next one. This uses \\( O(n\log n) \\) bits of working space, but repeats the \\( O(n) \\) lifting steps for each of the \\( n \\) coordinates, giving \\( \widetilde O(n^3m) \\) bit operations. For \\( m=O(n) \\), this is roughly \\( n^4 \\).

We would like to avoid this extra factor of \\( n \\) in the running time by computing all coordinates together while storing only a short approximation of each.

## The second attempt: make the solution integral

Let \\( \Delta := \det A \\) and \\( x^\star := A^{-1}b \\). Cramer's rule tells us that

$$
y=\Delta x^\star
$$

is an integer vector. We can therefore solve

$$
Ay=\Delta b
$$

by lifting its integer digits, then divide the result by \\( \Delta \\). An integer answer avoids coordinate-by-coordinate rational reconstruction.

Note that rational reconstruction does not need a known denominator. However, knowing the common denominator \\( \Delta \\) lets us approximate the integer vector \\( y \\) directly. For a coordinate of \\( y \\), we can retain only the most significant \\( p \\)-adic digits in the lifting and round away the lower ones, using \\( O(\log n) \\) bits per coordinate. **Dividing by \\( \Delta \\) preserves the entrywise approximation guarantee.** This lets us accumulate approximations to all coordinates together without storing all \\( O(n) \\) modular residues.

Computing \\( \Delta \\) also fits in linear space. We compute its residues modulo small primes using finite-field determinant algorithms based on Wiedemann, then combine the residues by the Chinese Remainder Theorem. Only one large integer needs to be stored, rather than a vector of large integers.

This removes the need to reconstruct fractions one at a time. However, there is still one memory problem remaining: although \\( b \\) has short entries, \\( \Delta b \\) can have \\( O(n\log n) \\) bits per entry. Applying the lifting recurrence directly to this vector again requires quadratic working storage.

## Store the carry instead of the large residual

Recall the notation from Dixon's algorithm. Here \\( x\_k \\) is the \\( k \\)-th p-adic digit of the integer solution \\( y \\), and

$$
s\_k=x\_0+x\_1p+\cdots+x\_{k-1}p^{k-1}
$$

contains the digits computed so far. For \\( Ay=\Delta b \\), the residual is \\( r\_k=(\Delta b-As\_k)/p^k \\), starting with \\( r\_0=\Delta b \\). Each lifting step satisfies

$$
Ax\_k\equiv r\_k\pmod p,
\qquad
r\_{k+1}=\frac{r\_k-Ax\_k}{p}.
$$

Keeping \\( r\_k \\) only modulo \\( p \\) is enough to find the current digit, but not to update the residual: dividing by \\( p \\) requires information that was discarded. Storing the full vector \\( r\_k \\) would again require quadratic space.

To overcome this space bottleneck, we propose storing the carry \\( c\_k=\lfloor As\_k/p^k\rfloor \\) instead of the full residual. It records how the digits already computed contribute to higher positions when multiplied by \\( A \\). All floors are taken coordinatewise. Since \\( r\_k \\) is integral, the fractional parts of \\( \Delta b/p^k \\) and \\( As\_k/p^k \\) cancel, giving

$$
r\_k=
\left\lfloor\frac{\Delta b}{p^k}\right\rfloor
-c\_k.
$$

We can recompute the first term one coordinate at a time from the stored determinant and the read-only vector \\( b \\). Together with the carry, this gives \\( r\_k\bmod p \\) for the next finite-field solve. After finding \\( x\_k \\), we update the carry by

$$
c\_{k+1}=\left\lfloor\frac{c\_k+Ax\_k}{p}\right\rfloor.
$$

This follows from \\( s\_{k+1}=s\_k+p^k x\_k \\): the fractional part of \\( As\_k/p^k \\) does not affect the floor after division by \\( p \\).

The carry stays small because every coordinate of \\( s\_k/p^k \\) lies in \\( [0,1) \\). Each carry entry is therefore bounded in absolute value by the absolute row sum of \\( A \\), which is polynomial in \\( n \\). Thus the carry needs only \\( O(\log n) \\) bits per coordinate. 
<!-- Together with the stored determinant and Wiedemann's solver, this lets us generate the digits \\( x_0, x_1, x_2, \dots \\) using \\( O(n\log n) \\) bits of working space. -->

## From digits to an approximate answer

Each lifting iteration computes \\( r\_k\bmod p \\), generates \\( x\_k \\), and updates \\( c\_k \\). This requires only \\( O(1) \\) vectors with \\( O(\log n) \\)-bit entries, together with the stored determinant. Thus we can generate the digits using \\( O(n\log n) \\) bits of working space.

The remaining challenge is to turn these digits into an approximate solution. The vectors \\( x\_0,x\_1,x\_2,\ldots \\) arrive one at a time, like a stream. Storing all \\( O(n) \\) vectors and reconstructing the answer afterward would again cost quadratic space. We must instead update our approximation as each vector arrives, then discard that vector.

For nonnegative integer coordinates, we maintain a short floating-point approximation to the running sum. When \\( x\_k \\) arrives, we add \\( p^k x\_k \\) and round each coordinate, retaining only its most significant bits and an exponent. This uses \\( O(\log n) \\) bits per coordinate. We choose enough precision to meet the entrywise \\( \epsilon \\)-approximation guarantee after all lifting steps.

Negative coordinates need more care. For a large modulus \\( P \\), \\( -10 \\) is represented by \\( P-10 \\). A \\( (1\pm\epsilon) \\) approximation to \\( P-10 \\) does not necessarily give a \\( (1\pm\epsilon) \\) approximation to \\( 10 \\) after subtracting from \\( P \\): an error that is small compared with \\( P-10 \\) can be large compared with \\( 10 \\).

Since we do not know each coordinate's sign in advance, we accumulate short approximations to both its digits and their complement. The complement, followed by adding \\( 1 \\), represents the negative counterpart. For \\( -10 \\), this gives a direct approximation to \\( 10 \\) without subtracting two large numbers. With a sufficiently large modulus, the smaller of the two accumulations gives the magnitude and identifies the sign.

## Wrap-up

For polynomially bounded input and inverse-polynomial accuracy, this yields a randomized algorithm with high-probability guarantees, \\( \widetilde O(n^2m) \\) bit operations, and \\( O(n\log n) \\) bits of working space. For a very sparse matrix, the time is \\( \widetilde O(n^3) \\). The guarantee is entrywise multiplicative, and there is no condition-number assumption. 

As applications, our solver also leads to algorithms for regression, linear programming, eigenvalue problems, and singular value decomposition using small working space.

# Kelner's algorithm: choose an easier modular system

Kelner's very recent breakthrough \[[Kel26](https://arxiv.org/abs/2609.38101)\] gives a faster algorithm for sparse numerical linear systems. It uses Dixon's p-adic lifting. The key idea is extremely clean and clever: change the system before lifting so that the modular solves become trivial.

Instead of solving \\( Ax = b \\), solve

$$
(PA+I)\widehat x=Pb.
$$

Since \\( PA+I\equiv I\pmod P \\), its modular inverse is the identity. Starting from \\( r\_0=Pb \\), the digit recurrence becomes

$$
x\_k=r\_k\bmod P,\qquad
r\_{k+1}=\frac{r\_k-x\_k}{P}-Ax\_k.
$$

No finite-field solve is needed at each iteration. There are \\( O(n) \\) iterations, each with a sparse matrix-vector product on \\( O(\log P) \\)-bit integers. Fast rational reconstruction recovers \\( \widehat x \\).

The returned vector solves \\( (A+I/P)\widehat x=b \\). Since \\( A \\) is a nonsingular integer matrix, \\( \\|A\\|\_2\geq1 \\) and hence \\( \\|A^{-1}\\|\_2\leq\kappa \\). Choosing \\( P\geq2\kappa/\epsilon \\) therefore gives the normwise approximation guarantee from [Definition 3](#approximation-guarantees):

$$
\\|\widehat x-x^\star\\|\_2
\leq \frac{\\|A^{-1}\\|\_2}{P-\\|A^{-1}\\|\_2}\\|x^\star\\|\_2
\leq\epsilon\\|x^\star\\|\_2.
$$

After normalization and input/output rounding, the algorithm achieves this guarantee in \\( \widetilde O(mn\log(\kappa/\epsilon)) \\) bit operations for short input entries.
 <!-- It is deterministic and can find a suitable scale without a supplied condition-number bound. -->

For very sparse, polynomially conditioned systems and inverse-polynomial accuracy, this gives \\( \widetilde O(n^2) \\) time, with a storage upper bound of \\( \widetilde O(n^2) \\) bits in this regime.
<!-- 
# Summary

The three algorithms use modular information in different ways. Dixon extracts digits and reconstructs a rational answer. Our algorithm changes the representation of the lifting state so that a rational system can be solved using linear working space. Kelner changes the system so that modular inversion becomes trivial and lifting uses sparse matrix-vector products.

Their guarantees also differ. Our solver provides an entrywise approximation guarantee without a conditioning assumption. Kelner's solver provides a normwise approximation guarantee with a running time that depends logarithmically on conditioning and accuracy.

Exact modular computations can produce rational and numerical answers. The main choices are which digits to compute, which information to retain, and how to recover the final solution.

# References

**[DDH07]** James Demmel, Ioana Dumitriu, and Olga Holtz. [Fast linear algebra is stable](https://doi.org/10.1007/s00211-007-0114-x). *Numerische Mathematik*, 108(1):59–91, 2007. [arXiv version](https://arxiv.org/abs/math/0612264).

**[Dix82]** John D. Dixon. [Exact solution of linear equations using \\( p \\)-adic expansions](https://doi.org/10.1007/BF01459082). *Numerische Mathematik*, 40:137–141, 1982.

**[EK97]** Wayne Eberly and Erich Kaltofen. [On Randomized Lanczos Algorithms](https://cspages.ucalgary.ca/~eberly/Research/Papers/lanczos_with_proofs.pdf). In *Proceedings of the 1997 International Symposium on Symbolic and Algebraic Computation (ISSAC)*, pages 176–183, 1997.

**[Hig11]** Nicholas J. Higham. [Gaussian elimination](https://doi.org/10.1002/wics.164). *WIREs Computational Statistics*, 3(3):230–238, 2011. [Author manuscript](https://eprints.maths.manchester.ac.uk/1579/1/lu5a.pdf).

**[Kel26]** Jonathan A. Kelner. [Solving Linear Systems in \\( \widetilde{O}(mn\log(\kappa/\epsilon)) \\) Bit Operations](https://arxiv.org/abs/2609.38101). arXiv:2609.38101, 2026.

**[LNY26]** Yiping Liu, Hoai-An Nguyen, and Junzhao Yang. [Numerical Linear Algebra in Linear Space](https://doi.org/10.1137/1.9781611978971.230). In *Proceedings of the 2026 Annual ACM-SIAM Symposium on Discrete Algorithms (SODA)*, pages 6392–6435, 2026. [arXiv version](https://arxiv.org/abs/2507.02433).

**[MMS18]** Cameron Musco, Christopher Musco, and Aaron Sidford. [Stability of the Lanczos Method for Matrix Function Approximation](https://doi.org/10.1137/1.9781611975031.105). In *Proceedings of the Twenty-Ninth Annual ACM-SIAM Symposium on Discrete Algorithms (SODA)*, pages 1605–1624, 2018. [arXiv version](https://arxiv.org/abs/1708.07788).

**[Nie22]** Zipei Nie. [Matrix anti-concentration inequalities with applications](https://arxiv.org/abs/2111.05553). In *Proceedings of the 54th Annual ACM SIGACT Symposium on Theory of Computing (STOC)*, pages 568–581, 2022.

**[PV21]** Richard Peng and Santosh S. Vempala. [Solving Sparse Linear Systems Faster than Matrix Multiplication](https://doi.org/10.1137/1.9781611976465.31). In *Proceedings of the 2021 ACM-SIAM Symposium on Discrete Algorithms (SODA)*, pages 504–521, 2021. [arXiv version](https://arxiv.org/abs/2007.10254).

**[She94]** Jonathan Richard Shewchuk. [An Introduction to the Conjugate Gradient Method Without the Agonizing Pain](https://www.cs.cmu.edu/~quake-papers/painless-conjugate-gradient.pdf). School of Computer Science, Carnegie Mellon University, 1994.

**[Wie86]** Douglas H. Wiedemann. [Solving sparse linear equations over finite fields](https://doi.org/10.1109/TIT.1986.1057137). *IEEE Transactions on Information Theory*, 32(1):54–62, 1986. -->
