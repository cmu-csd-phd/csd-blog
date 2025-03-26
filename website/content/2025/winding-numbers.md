+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "Winding numbers: a topological tool for geometry processing"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2025-03-26

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Graphics"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
# Consider these similar to keywords specified for a research paper.
tags = ["geometry-processing", "partial-differential-equations", "shape-analysis"]

[extra]
author = {name = "Nicole Feng", url = "https://nzfeng.github.io" }
# The committee specification is  a list of objects similar to the author.
committee = [
    {name = "Jun-Yan Zhu", url = "https://www.cs.cmu.edu/~junyanz/"},
    {name = "Minchen Li", url = "https://www.cs.cmu.edu/~minchenl/"},
    {name = "Arjun Teh", url = "https://www.cs.cmu.edu/~ateh/"}
]
+++

<!-- After filling in the above "top-matter", as per instructions provided
in the `.md` file, you can write the main body of the blogpost here
onwards. Commonly used examples of syntax are shown below.

You can run `./local_server.sh` at the root of the repository to see
how the final blogpost looks in action. -->

This post explains the key findings and algorithm of our 2023 SIGGRAPH paper ["Winding Numbers on Discrete Surfaces"](https://nzfeng.github.io/research/WNoDS/index.html).

# What problem does this paper solve?

For a given point on a surface, we would like to know whether it is inside or outside a given curve.

For example, coloring points on this cow according to inside vs. outside would look like this:

<img style="width:50%; display:block; margin:auto;" src="./figures-02.png" alt="Basic problem of determining the inside/outside of a curve, demonstrated using a cow."></img>

Of course, before asking _how_ to determine inside/outside, we should ask whether it's always _possible_ to define inside/outside. At least in the Euclidean space \\(\mathbb{R}^2\\), the [_Jordan curve theorem_](https://en.wikipedia.org/wiki/Jordan_curve_theorem) guarantees that every simple planar closed curve separates \\(\mathbb{R}^2\\) into an inside region and an outside region. And a similar statement is also true for "simple" surfaces like the above cow.

But on some surfaces, not all closed curves bound regions:

<img id="" style="width:60%; display:block; margin:auto;" src="./figures-06.png" alt="'Bounding' vs. 'non-bounding' loops demonstrated using Planet Cow."></img>

On the left, a fence on Planet Cow forms a closed curve, and the cows are confined to one region. But the fence on the right also forms a closed curve with no gaps, and yet the cows are free to roam wherever they'd like. 

We'll call curves like the one on the left _bounding_, because they bound a region, and curves like the one on the right _nonbounding_ because they don't bound regions. So far, we've established that while inside/outside is not well-defined for nonbounding curves, inside/outside is at least well-defined for bounding curves.

However, an algorithm for computing inside/outside is not so simple as classifying loops as "bounding" vs. "nonbounding". In particular, nonbounding loops can combine to bound valid regions (figure reproduced from <a href="https://marzia-riso.github.io/assets/boolsurf/boolsurf_paper.pdf">Riso et al. 2022, Fig. 4</a>):

<img id="" style="width:50%; display:block; margin:auto;" src="./figures-03.png" alt="An example showing why we cannot simply discard nonbounding curves."></img>

And more generally, there are numerous ways inside/outside can fail to be well-defined if we're willing to consider _all_ types of surface domains:

<img id="" style="width:90%; display:block; margin:auto;" src="./BasicProblem.png" alt="The basic problem, demonstrated on a variety of general surfaces."></img>

Computing inside/outside gets even harder if some of the curves have been corrupted somehow and are now "broken", for example the "dashed" curves in the rightmost example above, which represent partial observations of an originally whole curve. Ideally, we would like to answer "inside or outside?" for the point \\(p\\) in all of the examples shown above.

Our starting point to reasoning about all of the above is the <i>winding number</i>, a quantity which appears widely across math and physics. Intuitively, the winding number at a point \\(p\\) measures the infinitesimal angle subtended by the curve at \\(p\\), and sums up all these angles over the curve. For a closed curve in the plane, this gives us a piecewise constant function whose value at each point tells us how many times the curve "winds" around it. Hence winding number is fundamentally a _topological_ quantity (though it is often defined through a geometric formula). One can also consider a generalization of winding number called _solid angle_, which considers open curves in addition to closed curves.

<img id="" style="width:70%; display:block; margin:auto;" src="./figures-07.png" alt="Basic definition of winding number."></img>

Researchers in computer graphics and geometry processing have in fact already used the properties of solid angle to great success. Perhaps the most well known examples are the equivalent* methods of _Poisson Surface Reconstruction_ <a href="https://hhoppe.com/poissonrecon.pdf">[Kazhdan et al. 2006]</a> and _generalized winding number_ <a href="https://igl.ethz.ch/projects/winding-number/">[Jacobson et al. 2013]</a> (\*see <a href="https://imaging.cs.cmu.edu/fast_dipole_sums/#paper">Chen et al. 2024</a> for a precise explanation of the equivalence). However, all past methods are only applicable to Euclidean domains like \\(\mathbb{R}^n\\), not general surface domains. For deeper discussion of why usual interpretations of solid angle don't apply in surface domains, see our supplemental, <a href="https://nzfeng.github.io/research/WNoDS/PerspectivesOnWindingNumbers.pdf">"Perspectives on Winding Numbers"</a>.

At the time of our work, there had been relatively little mathematical or algorithmic treatment of winding number on surfaces. <a href="https://marzia-riso.github.io/assets/boolsurf/boolsurf_paper.pdf">Riso et al. 2022</a> had recently developed the algorithm "BoolSurf" for computing booleans on surfaces &mdash; but assumed that the input curves are closed, and already partitioned into loops. It remained an open question of how one could optimally infer the curve's topology from unstructured input. More generally, we aimed for a principled handling of surfaces with boundary, and other types of surfaces. 

Concretely, our algorithm does the following: Given an unorganized collection of curves with orientations -- meaning each curve has a specified direction from one endpoint to the other, but otherwise with no additional structure -- we determine inside vs. outside on general surfaces. Importantly, we do so _robustly_, meaning the algorithm reliably outputs correct answers even in the presence of noise and errors. In the process, we determine the bounding vs. nonbounding components of the curve, and produce a closed, completed version of the input curve.

<img id="" style="width:100%; display:block; margin:auto;" src="./figures-15.png" alt="A collection of results from the paper."></img>

In short, we obtain an algorithm that answers the fundamental question of inside/outside. In turn, the algorithm can form a basic building block of many geometry processing tasks ranging from region selection to curve completion to boolean operations on shapes.

<img id="" style="width:60%; display:block; margin:auto;" src="./Booleans.png" alt="An example of doing robust booleans between broken shapes on surfaces."></img>
<br>
<span style="display:block; margin:auto; text-align: center; font-size: 0.8rem;">An example of using our algorithm to compute boolean operations on regions defined by imperfect, broken curves on surfaces.</span>

# How does the paper solve the problem?

**In a nutshell**: the key idea of our method is to turn the harder problem of determining inside/outside of arbitrary _curves_, into an easier, but equivalent problem about _vector fields_. 

As mentioned earlier, we start from the established concept of _winding number_. Ordinary winding number is often presented as an integral: for example, in differential geometry, the winding number \\(w_\Gamma(x)\\) of a curve \\(\Gamma\\) at a point \\(x\in\mathbb{R}^2\\) is usually defined as \\(w_\Gamma(x)=\frac{1}{2\pi}\int_\Gamma \frac{\langle n_\Gamma(y), y-x\rangle}{\|x-y\|^2} {\rm d}y \\), or equivalently in complex analysis as the complex contour integral \\(w_\Gamma^\mathbb{C}(p) = \frac{1}{2\pi i}\int_\Gamma \frac{1}{z-p} {\rm d}z\\) for \\(p\in\mathbb{C}\\). You could, for example, extend these integral definitions to surfaces that admit planar or spherical parameterizations. But in general, these contour integrals can't easily be computed on surfaces. There are several other characterizations of winding numbers (see <a href="https://nzfeng.github.io/research/WNoDS/PerspectivesOnWindingNumbers.pdf">"Perspectives on Winding Numbers"</a>), but they also fail to generalize on surfaces.

One insight is that the winding number is a special type of <a href="https://en.wikipedia.org/wiki/Harmonic_function">_harmonic function_</a>. A harmonic function is one whose Laplacian vanishes; you can just think of it as a special type of smooth function. In particular, winding number is a <i>jump harmonic function</i> (for more detail, see the section below, "The algorithm in more detail").

Jump harmonic functions can be computed using the <i>jump Laplace equation</i>, which is the partial differential equation (PDE) version of _solid angle_, a generalization of winding number to open curves \\(\Gamma\\); from this point on, we'll use the terms "winding number" and "solid angle" interchangeably. Simply solving the jump Laplace equation, however, doesn't yield a winding number function on surfaces, because of the influence of nonbounding loops. In particular, we get spurious discontinuities that do not correspond to anything in the input:

<img id="" style="width:50%; display:block; margin:auto;" src="./JumpHarmonicNonBounding.png" alt="Figure demonstrating what happens if we just solve for the jump harmonic function corresponding to a nonbounding looop - we get spurious boundaries that do not correspond to anything in the input."></img>

Formally, (non)bounding loops are loops that are <i>(non-)nullhomologous</i>, meaning congruent to zero in the first homology group \\(H_1(M) = \rm{ker}(\partial_1)\setminus\rm{im}(\partial_2)\\) of the surface \\(M\\). In words, nonbounding loops are closed curves which don't bound regions.

<img id="" style="width:80%; display:block; margin:auto;" src="./figures-11.png" alt="Figures more clearly demonstrating bounding vs. nonbounding curves."></img>

<!-- The elements of the first homology group are called homology classes: they are equivalence classes representing cycles that differ only by the addition of the boundary of some region. -->
Great, we've identified the core challenge of our problem! We've been able to formalize the meaning of "nonbounding" through the lens of homology: in particular, we just need to determine the _homology class_ of the curve (meaning the nonbounding components of the curve which belong to the first homology group of \\(M\\)). But homology only directly applies to closed curves. So we use <i>de Rham cohomology</i> to instead process _functions_ dual to curves. 

At a high level, we start by taking an appropriate derivative of our jump harmonic function. Once in the "gradient domain", our problem of decomposing a curve into its bounding and nonbounding components &mdash; meaning components that can and cannot be explained as region boundaries &mdash; becomes the more well-studied problem of decomposing a vector field into components that can and cannot be explained by a potential, which we can solve using the classical tool of _Hodge decomposition_.

<img id="" style="width:80%; display:block; margin:auto;" src="./figures-17.png" alt="An overview of the steps of our algorithm, using visual results."></img>

**This is a key insight of our method:** Given some unstructured collection of broken curves, it's really hard to reason about them directly. So we instead transform the curves into _vector fields_, which are objects we do know how to reason about -- and in particular, know how to decompose using Hodge decomposition. Once we have the decomposition of the vector field, we transform it into a decomposition of the curve.

Further, because we work with smooth functions defined globally on the domain, our algorithm is much more robust than if we had tried to work directly with sparse, singular curves. In summary, the final algorithm is able to robustly compute inside/outside by determining the curve's nonbounding components, in particular by reasoning about vector fields associated with the curve rather than the curve itself. The algorithm is guaranteed to work if the input is "perfect" (no noise, gaps, etc.), and otherwise degrades gracefully in the presence of imperfections (Figures 12--15, 20--26 in the paper.)

## The algorithm in more detail

<!-- Discretely, we represent curves and regions as <i>chains</i> on a triangulated surface. The resulting algorithm entails solving a sparse linear system (Laplace equation) with the usual cotan-Laplace operator. On surfaces of nontrivial topology, we solve another sparse linear system (another Poisson problem) for the Hodge decomposition, and a sparse linear system to map the decomposition of our 1-form to a decomposition of our curve. -->

We use \\(M\\) to denote a surface domain, and \\(\Gamma\\) some collection of oriented curves on \\(M\\). As input, the algorithm takes in \\(M\\) and \\(\Gamma\\). As output, the algorithm outputs
* an integer labeling of regions bounded by \\(\Gamma\\)
* a decomposition of \\(\Gamma\\) into bounding components that induce valid regions vs. nonbounding components
* a closed, completed version of the input curve \\(\Gamma\\).

As mentioned above, winding number is a <i>jump harmonic function</i>, meaning a function that is harmonic everywhere &mdash; including at points on the curve &mdash; modulo the jumps. (The function only fails to be harmonic at the curve's endpoints where there is a branch point singularity, shown below.)

<img id="" style="width:80%; display:block; margin:auto;" src="./figures-12.png" alt="Figures demonstrating the jump harmonic properties of solid angle."></img>

Hence our starting point to winding numbers on surfaces is the <i>jump Laplace equation</i> defined on a domain \\(M\\),
<img id="" style="width:20%; display:block; float:right; margin-right: 10%;" src="./figures-14.png" alt="An inset figure showing a local neighborhood of a point on the 'jump'."></img>
\\[
    \begin{align*}
    \Delta u(x) &= 0 &x\in M\setminus\Gamma \newline
    u^+(x) - u^-(x) &= 1^* &x\in \Gamma \newline
    \frac{\partial u^+}{\partial n}(x) &= \frac{\partial u^-}{\partial n}(x) &x\in \Gamma
    \end{align*}
\\]
<span style="display:block; margin:auto; text-align: right; font-size: 0.7rem;">*More generally, \\(u^+(x) - u^-(x) = \\) number of times \\(\Gamma\\) covers \\(x\\).</span>
            
Basically, the jump Laplace equation corresponds to the standard Laplace equation \\(\Delta u=0\\) (which defines a standard harmonic function), plus a condition that stipulates the solution must jump by a specified integer across the curve \\(\Gamma\\). Finally, the third equation is a compatibility condition that ensures the solution is indeed harmonic "up to jumps" everywhere on \\(M\setminus\partial\Gamma\\). Intuitively, for all \\(x\notin\Gamma\\) the function \\(u(x)\\) is harmonic in the usual sense, and for \\(x\in\Gamma\\) (where the jump occurs) it's still possible to locally shift \\(u\\) such that it once again becomes harmonic in the usual sense (above, right).

Assuming \\(M\\) is _simply-connected_, meaning there cannot exist nonbounding loops on \\(M\\), then we can simply solve the jump Laplace equation above for the function \\(u(x)\\). If \\(\Gamma\\) is closed, this case is analogous to ordinary winding number in the plane, which yields a piecewise constant, integer-valued function; every component of \\(\Gamma\\) is a bounding component.

<img id="" style="width:80%; display:block; margin:auto;" src="./JumpHarmonic.png" alt="Winding number as an integer-valued jump harmonic function, both in the plane, and on a simply-connected surface."></img>

If \\(\Gamma\\) is not closed (but \\(M\\) is still simply-connected), then \\(u(x)\\) yields a "soft" real-valued (rather than integer-valued) indicator function, analogous to solid angle.

Solving the jump Laplace equation above is Step \\(\raisebox{.5pt}{\textcircled{\raisebox{-.9pt}{1}}}\\). If \\(M\\) is not simply-connected, we need to take additional steps. The key insight here is that jump harmonic functions form the "bridge" through which we can transform curves into functions, and vice versa. In particular, jump harmonic functions can both encode curves (where the function jumps in value) as well as a curve's homology class (through its derivative). Our algorithm will amount to a round-trip around the following diagram, where we first translate the input curve \\(\Gamma\\) into a jump harmonic function, then into a <i>differential 1-form</i>, which you can think of as a vector field. We'll then translate the resulting 1-form back into a jump harmonic function and curve, which will correspond to our final winding number function and curve decomposition, respectively. Performing these translations amounts to using appropriate notions of differentiation and integration.

<img id="" style="width:60%; display:block; margin:auto;" src="./figures-18.png" alt="A diagram showing the steps of our algorithm."></img>

At a high level, these notions of differentiation and integration simply correspond to their usual notions from ordinary calculus, except we have to take extra care when dealing with the discontinuities of jump harmonic functions. For simplicity, we'll first consider a periodic 1-dimensional function \\(f(x)\\) defined on the unit interval \\([0,1]\\): 

<img id="" style="width:70%; display:block; margin:auto;" src="./DarbouxDerivative.png" alt="1D example of the Darboux derivative."></img>

In general, the gradient of such a function \\(f(x)\\) with respect to \\(x\\) yields a continuous part \\(\omega:=\mathcal{D}f\\), obtained from considering each continuous interval of \\(f(x)\\), as well as a "jump" part \\(\mathcal{J}f\\) encoding the location and magnitude of the jumps in \\(f(x)\\), expressed here as a sum of Dirac-deltas.

For a jump _harmonic_ function in particular, the continuous part \\(\omega:=\mathcal{D}f\\), which we term the _Darboux derivative_, "forgets" jumps:

<img id="" style="width:70%; display:block; margin:auto;" src="./JumpHarmonicDerivative.png" alt="1D example of the Darboux derivative of a jump harmonic function."></img>

(If you're familiar with differential geometry, you can think of \\(\mathcal{D}f\\) as "\\(df\\) modulo jumps", where \\(d\\) denotes the standard exterior derivative. Just as the standard exterior derivative \\(df\\) measures the failure of \\(f\\) to be constant, \\(\mathcal{D}f\\) measures the failure of \\(f\\) to be _piecewise_ constant.) In essence, even though jump harmonic functions have discontinuities, the condition of harmonicity forces the Darboux derivative of a jump harmonic function to be globally continuous because the derivatives must "match up" across the discontinuity.

Because the Darboux derivative of a jump harmonic function "forgets" the jumps, there is no unique inverse to Darboux differentiation. In particular, we can only integrate "up to jumps": to continue the previous example, both the original jump harmonic function \\(f(x)\\) and the function \\(g(x)\\) shown below are valid possibilities of integrating \\(\omega\\):

<img id="" style="width:70%; display:block; margin:auto;" src="./DarbouxDerivativeIntegration.png" alt="1D example of integration of a Darboux derivative."></img>

The moral of this story is that to map from derivatives back to curves, we can integrate \\(\omega\\) and _choose_ the jumps. (This choice of jumps is what will allow us to decompose curves into bounding vs. nonbounding components.)

Our understanding of the 1D case more or less extends directly to the 2D case. Instead of a 1D function on a periodic interval, we can, for example, consider a solution \\(u(x)\\) of the jump Laplace equation on a 2D periodic domain &mdash; namely, a torus:

<img id="" style="width:50%; display:block; margin:auto;" src="./2DAnalogy.png" alt="Generalization from the previous 1D example to 2D surfaces."></img>

We arrive at Step \\(\raisebox{.5pt}{\textcircled{\raisebox{-.9pt}{2}}}\\): taking the Darboux derivative of the jump harmonic function obtained in Step \\(\raisebox{.5pt}{\textcircled{\raisebox{-.9pt}{1}}}\\). The Darboux derivative \\(\omega\\) of \\(u\\) is now a 1-form, which can be thought of as a vector field (shown above). If \\(\omega=0\\), then \\(u(x)\\) is piecewise constant, meaning that \\(u(x)\\) is already a valid (piecewise constant) region labeling. Conversely, if \\(w\neq 0\\), then there are nonbounding components of \\(\Gamma\\). In particular, nonbounding components of \\(\Gamma\\) are encoded by the _harmonic_ component \\(\gamma\\) of the 1-form \\(\omega\\). More formally, (non)bounding components of \\(\Gamma\\) correspond to 1-forms (non)congruent to zero in the first cohomology group \\(H^1(M)=\rm{ker}(d_1)\setminus\rm{im}(d_0)\\). 

Luckily for us, extracting the harmonic component of 1-form can be done via _Hodge decomposition_, which states that our 1-form \\(\omega\\) can be decomposed as \\(\omega=d\alpha+\delta\beta+\gamma\\), where \\(\gamma\\) is the harmonic 1-form we seek to isolate (and the differential forms \\(\alpha\\) and \\(\beta\\) are some scalar and vector potentials). So Step \\(\raisebox{.5pt}{\textcircled{\raisebox{-.9pt}{3}}}\\) amounts to doing Hodge decomposition to extract the harmonic 1-form \\(\gamma\\).

In summary, we have transformed our original problem of decomposing the input curve into components that can and cannot be explained as region boundaries, into the well-studied problem of decomposing a vector field into components that can and cannot be explained by a potential.

<!-- The strength of \\(\gamma\\) tells us about the "strength" of the nonbounding component present in the curve \\(\Gamma\\). -->

To recap, here is where we are in our round-trip journey so far, using as a visual example a collection of (broken) bounding and nonbounding loops \\(\Gamma\\) on a torus:
<img id="" style="width:60%; display:block; margin:auto;" src="./OneWayJourney.png" alt="Recap of our algorithmic journey so far."></img>

We've used differentiation to obtain a 1-form associated with the original curve \\(\Gamma\\), then use Hodge decomposition to process this 1-form into a harmonic 1-form \\(\gamma\\) encoding the nonbounding component of \\(\Gamma\\). We arrive at Step \\(\raisebox{.5pt}{\textcircled{\raisebox{-.9pt}{4}}}\\): To determine our curve decomposition, we just have to use integration to translate \\(\gamma\\) back into a jump harmonic function, and then a curve that will represent the nonbounding component of \\(\Gamma\\). 

More specifically, we search for a scalar potential \\(v\\) that could have generated \\(\gamma\\), meaning \\(\mathcal{D}v=\gamma\\). Since \\(\gamma\\) is harmonic, \\(v\\) must jump somewhere; but remember, we get to choose these jumps &mdash; and we want the _jump derivative_ \\(g:=\mathcal{J}v\\) to represent the nonbounding component of \\(\Gamma\\). We formulate the following optimization that does just this:

<img id="" style="width:90%; display:block; margin:auto;" src="./IntegrationOptimization.png" alt="The optimization formulation of the integration procedure."></img>

In words, the first constraint \\(\mathcal{D}v=\gamma\\) stipulates that the solution \\(v\\) should integrate \\(\gamma\\) in the "Darboux" sense, while the second term in the objective function encourages the jumps \\(g=\mathcal{J}v\\) in \\(v\\) to concentrate on a subset of the original curve \\(\Gamma\\). In the case that \\(\Gamma\\) is a broken curve, the first term in the objective function also encourages \\(g=\mathcal{J}v\\) (which necessarily must form closed loops, since \\(\gamma\\) is harmonic and thus not globally integrable) to be a _shortest_ closed-curve completion of the nonbounding components of \\(\Gamma\\). Finally, the second constraint discourages spurious extraneous loops in the case that \\(\Gamma\\) contains multiple nonbounding components of the same homology class.

The solution of this optimization yields a so-called "residual function" \\(v\\) such that the solution \\(w\\) to a jump Laplace equation using the curve \\(\Gamma - \mathcal{J}v\\) is our final winding number function. In other words, we solve for the function \\(w\\) for which we have removed the influence of \\(\Gamma\\)'s nonbounding components. 

Step \\(\raisebox{.5pt}{\textcircled{\raisebox{-.9pt}{5}}}\\) is simply reading off the curve decomposition from the residual function \\(v\\). The locus of points \\(\mathcal{J}v\\) where \\(v\\) jumps represents a completion \\(G\\) of the nonbounding components of the input curve \\(\Gamma\\); the bounding components of \\(\Gamma\\) are simply the complement of the nonbounding components, taken as a subset of \\(\Gamma\\). Additionally, the function \\(w\\) can be rounded to yield integer region labels \\(W\\). The entire algorithm is summarized in the following diagram:

<img id="" style="width:90%; display:block; margin:auto;" src="./CompleteRoundTrip.png" alt="The complete round-trip."></img>

<!-- <img id="" style="width:90%; display:block; margin:auto;" src="./NonOrientableSurfaces.png" alt="Non-orientable surfaces."></img>

<img id="" style="width:100%; display:block; margin:auto;" src="./RelativeHomology.png" alt="Relative homology."></img> -->

With our algorithm described, all that remains is to discretize the algorithm. 

In the discrete setting, we assume the surface domain \\(M\\) is specified as a triangle mesh. We represent curves and regions as <i>chains</i> on \\(M\\), meaning as signed integer-value functions on mesh edges and mesh faces, respectively. The jump Laplace equation can be discretized on the mesh as a sparse, positive definite linear system. Performing Hodge decomposition on the gradient of the solution \\(u\\) amounts to solving another Laplace-type sparse linear system. Finally, performing the integration procedure necessary to map the decomposition of our 1-form to a decomposition of our curve amounts to solving sparse linear program. (The last two steps are only necessary if \\(M\\) is topologically nontrivial.) For more details, check out <a href=
"https://nzfeng.github.io/research/WNoDS/WNoDS.pdf">our paper</a>, which also contains detailed pseudocode, or our <a href="https://github.com/nzfeng/SWN">code repository</a>.

# Takeaway

In summary, in this paper we addressed the problem of computing inside/outside of curves on surfaces, including the cases where curves fundamentally might not even have a well-defined inside or outside. We were able to do this by using a duality between curves and vector fields, using insights from differential geometry and algebraic topology.


<!-- # Additional technical details

Disclaimer: You do not need to understand these details to understand the paper! This section is here in case you fully read the paper and understand the algorithm, and have technical questions about certain algorithmic choices.

## What if the curve isn't constrained to mesh edges?

Our algorithm assumes the input curve \\(\Gamma\\) is restricted to mesh edges. Can we relax this assumption?

We can: Instead of a Laplace equation with jump conditions, we may consider an equivalent _Poisson_ equation with a source term encoding the gradient of an indicator function:
\\[
	\Delta u = \nabla\cdot N\mu_\Gamma.
\\]
The source term on the right-hand side corresponds to a singular vector field concentrated on \\(\Gamma\\), where the vectors align with the normals of the input curve. This in fact the perspective taken by the classic Poisson Surface Reconstruction algorithm &mdash; which, as noted earlier, is equivalent in some sense to solid angle.

We can discretize this Poisson equation using finite elements, although the solution is inevitably "smeared out" somewhat as a result of being regularized by the choice of function space. (In particular, continuous elements will yield approximation error when trying to represent a discontinuous function.)

<img id="" style="width:50%; display:block; margin:auto;" src="./figures-13.png" alt="An example of the results of our algorithm when the curve is not constrained to mesh edges."></img>

We can still take the derivative of this function in the same sense of our original algorithm, and Hodge-decompose. On the other hand, integration is less clean.

## A dual formulation

A curve can be viewed as the boundary of "weighted regions", where the weights are the winding numbers. Discretely, this means if we view the curve as a 1-chain \\(c\\) in a triangulation of the domain, then the winding number is a 2-chain \\(b\\) such that \\(\partial b=c\\).

<img id="" style="width:20%; display:block; margin:auto;" src="./figures-05.png" alt="A diagram showing how winding number can be interpreted as 'weighted regions'."></img>

This leads to a "dualized" formulation of the algorithm presented in our paper, where we solve for a dual 0-form (values per face) instead of a primal 0-form. If we encode the curve &Gamma; as a dual 1-chain, then the relationship "&Gamma; bounds a region \\(b\\)" can be expressed as the linear relation \\[db = c\\]

where \\(d\\) is the discrete exterior derivative acting on dual 0-forms, and the jump condition induced by &Gamma; is interpreted as a dual 1-form \\(c\\).

The least-squares solution is given by another Laplace equation, \\[d\ast db = d\ast c.\\]

<img id="" style="width:30%; display:block; margin:auto;" src="./figures-10.png" alt="A diagram showing how the 'dual jump Laplace equation' is derived."></img>

To identify the nonbounding components of the curve, one can do Hodge decomposition on the derivative, just as before (although the corresponding equations will also be appropriately "dualized").

The dual formulation streamlines certain concepts; for example, the "jump derivative" we define in Section 2.4 of <a href=
"https://nzfeng.github.io/research/WNoDS/WNoDS.pdf">the paper</a> simply becomes the usual boundary operator (we merely hint at this in Section 3.6.) Encoding the input curve as a dual 1-chain would have also subsumed more difficult situations on non-manifold and non-orientable meshes where primal 1-chains can't unambiguously specify the "sides" of the curve (see discussion in Section 2.2 and 3.7).

The dual algorithm is pretty much the same as the one presented in the paper since it solves the same linear systems and linear program, albeit on dual elements. On the other hand, the primal formulation will perhaps be more familiar to graphics practioners. For example, in the primal formulation, discretizing the jump Laplace equation yields the ordinary cotan-Laplace matrix on vertices, whereas in the dual formulation one would build an analogous cotan-Laplace matrix acting on 2-forms (though the latter isn't any more difficult to build than the former!) You also get better resolution by solving on corners (vertices), rather than on faces. In summary, one approach wasn't clearly better over the other, so we picked the more familiar primal formulation. -->