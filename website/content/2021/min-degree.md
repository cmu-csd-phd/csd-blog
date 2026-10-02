+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "A story about min-degree ordering"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2021-09-27

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Algorithm", "Graph Theory"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
# Consider these similar to keywords specified for a research paper.
tags = ["Min-degree ordering", "Gaussian Elimination"]

[extra]
# For the author field, you can decide to not have a url.
# If so, simply replace the set of author fields with the name string.
# For example:
#   author = "Harry Bovik"
# However, adding a URL is strongly preferred
author = {name = "Junxing Wang", url = "junxingwang.org" }
# The committee specification is simply a list of strings.
# However, you can also make an object with fields like in the author.
committee = [
    "Daniel Sleator",
    "Ellango Jothimurugesan",
    {name = "Fei Fang", url = "https://feifang.info/"},
]
+++

# Preview

In this blog, we are going to discuss an approach to computing min-degree ordering efficiently, which is an important heuristic used to speed up Gaussian Elimination. As we know, Gaussian Elimination is an algorithm for finding precise solutions of linear systems. It is widely used in many applications such as Matlab.

The critical part of the approach comes down to another classical math problem: how to estimate the size of the union of sets efficiently. We will associate these two fundamentally different problems by viewing the process of Gaussian Elimination from the perspective of the graph. Then we will showcase several techniques for estimating the size of the union of sets and construct a data structure to produce min-degree ordering efficiently.   

# Linear system

To begin with, we need to understand what linear systems are. In general, linear systems are mathematical models based on linear constraints. They play important roles in many different applications such as signal processing, telecommunications, and automatic control theory. 

Let’s look at the following example:
![eq1](../eq1.png)

This is a linear system with three variables \\(x_1,x_2,x_3\\) and three linear constraints shown as three equations above. Considering these three variables as a 3-dimensional vector \\(x=(x_1,x_2,x_3)^T\\), we can represent the linear system as the following matrix equation.
 ![eq2](../eq2.png)

In general, any linear system with n variables \\(x_1,x_2,...,x_n\\) and m constraints can be written as \\(Ax=b\\) where \\(x=(x_1,x_2,...,x_n)^T\\) is an n-dimensional vector representing n variables, A is a n-by-m constraint matrix and b is a m-dimensional constraint vector. In order to solve the linear system, we need to assign values to all the variables \\(x_1,x_2,...,x_n\\) to satisfy the equation \\(Ax=b\\). For example, \\(x=(1,2,3)^T\\) is a solution to the linear system in the example above.

Throughout history, people have developed many tools for solving linear systems. There are two important aspects of algorithm design for linear system solvers: the accuracy of the solution, and the performance of the algorithm. In general, the more precise solution we wish to get, the more time and larger space will be required. 

With respect to these two aspects, one might ask: 1) what is the fastest algorithm that gives approximate solutions to linear systems and 2) what is the fastest algorithm to solve linear systems precisely. For the first question, there exist algorithms that give approximate solutions in almost linear time of the input size of the system. In this article, we will focus on the second question. We are going to describe a classic precise linear system solver called Gaussian Elimination and talk about a heuristic called min-degree ordering to speed it up. 

For the ease of the discussion, we will only focus on the linear systems in which the linear constraint matrix is symmetric positive definite (SPD). Mathematically, a symmetric matrix A is SPD if \\(x^TAx>0\\) for any non-zero vector x. 

It is a reasonable assumption because the SPD matrices occur in many real world applications and have many good properties. First, all SPD matrices are symmetric. Second, all diagonal entries in the SPD matrix are non-zeros. These two properties will play important roles later on. In fact, SPD matrices are not required for solving linear systems in general.

# Gaussian Elimination

Now we will show how to use Gaussian Elimination to solve linear systems. Consider a linear system with n variables and n linear constraints. We use an n-dimensional vector \\(x=(x_1,x_2,...,x_n)^T\\) to denote the variables. We present these n linear constraints as \\(Ax=b\\), in which A is an n-by-n square SPD matrix and b is an n-dimensional vector. 

At a high level, we will choose a variable and “eliminate” its association from n-1 constraints without changing the original solution. These n-1 linear constraints form a new linear system with n-1 variables and n-1 constraints themselves. We will then solve that new linear system recursively, and finally take its solution back to the original linear system to get the full solution.  

To “eliminate” the variable, we consider these two operations: scaling one constraint by a constant factor, and subtracting one constraint from another. If the scale factor is not zero, it is easy to see that the solution of the original linear system is preserved under these two operations. From the matrix perspective, these two operations are interpreted as applying the same basic matrix row operations on both the constraint matrix A and the constraint vector b.

The goal can be achieved by zeroing out all but one element of one column of the matrix with these two operations. Because, once we have done that, the variable associated with that column will have coefficient 0's in n-1 linear constraints. In other words, these n-1 linear constraints form a new linear system without that variable involved.

To understand this process better, we will show how to eliminate variable x1 in the following linear system: 
 ![eq3](../eq3.png)

The goal here is to zero out the first column \\((1,1,2)^T\\) except the first entry. To turn the first entry of the second row \\((1,3,0)\\) into zero, we will subtract first row \\((1,1,2)\\) from it, and also subtract \\(b_1\\) from \\(b_2\\) in the constraint vector. Then we get the following partial result.
![eq4](../eq4.png)

In order to zero out the first entry of the third row, we have to scale the first row by a factor of 2 and then subtract it from the third row. We will also apply the same operations to the constraint vector to the right. Then we get the following linear system. 
  ![eq5](../eq5.png)
 
Notice that the second and third constraint above form a new linear system without variable \\(x_1\\), as shown below. To complete Gaussian Elimination, we will calculate \\(x_2\\) and \\(x_3\\) in this new linear system recursively.
 ![eq6](../eq6.png)

Finally, we will calculate \\(x_1\\) by taking \\(x_2\\) and \\(x_3\\) into the first constraint of the original linear system. Thus, we solve the linear system.   

So… what is the time complexity of Gaussian Elimination? 

Here is a simple analysis. In order to eliminate one variable, we need to take \\(O(n)\\) matrix row operations and each matrix row operation takes \\(O(n)\\) time. It also takes \\(O(n)\\) time to calculate each variable by taking the recursive solution into one linear constraint of the linear system at that step. Overall, we need to eliminate n-1 variables until the linear system becomes a trivial equation with one single variable involved. Hence, the total running time will be \\((O(n)O(n)+O(n))(n-1)=O(n^3)\\). 

Actually, the time complexity \\(O(n^3)\\) only gives us a loose upper bound on the actual running time. In practice, different linear system inputs and different orderings of the variables to eliminate can result in dramatically different running time. One extreme example is that it only takes \\(O(n)\\) time to solve any linear system of diagonal constraint matrix.

One may get the intuition that the more zeros there are in the constraint matrix, the less time it takes to finish the calculation. Because the more zeros there are in the constraint matrix, the fewer row operations are required to zero out a column of the matrix to eliminate a variable, also the less time it takes to complete one row operation. 

However, the number of zeros may change a lot during Gaussian Elimination. Let’s look at the following example of the linear system:
 ![eq7](../eq7.png)

Notice that the constraint matrix is quite sparse, i.e., has many zeros, at the beginning. Consider eliminating variable \\(x_1\\) at the first step. After doing eight matrix row operations, specifically, four row scalings and four row subtractions, we will get a super “dense” submatrix, i.e., without any zero entry:
 ![eq8](../eq8.png)

However, if we were to, instead, eliminate variable \\(x_2\\) in the first step, we would use only two matrix row operations and get a very sparse matrix:
 ![eq9](../eq9.png)

In conclusion, the choice of which variable to eliminate at each step may result in completely different matrices and incur dramatically different running times. Therefore, the ordering of the variables to eliminate during Gaussian Elimination is a very important factor of the actual total running time. 

So… what is the ordering of the variables to eliminate during Gaussian Elimination that minimizes the total running time?

This is a very important question for both theoretical and empirical reasons. In practice, once the computer knows the “best” ordering in advance, it can pre-permute the rows and columns of the matrix so that the non-zero entries are mostly clustered in blocks. Such preprocessing will provide a huge boost to the performance during Gaussian Elimination because computation involving consecutive memory can be done much faster in cache. 

Unfortunately, Yannakakis showed that it is an NP-hard problem to find an optimal ordering for Gaussian Elimination back in 1981. This negative result is not the end of the story. Eventually, people realized that a simple “greedy” ordering for Gaussian Elimination performs really well in the practice. The “greed” comes from the strategy of always choosing the variable to eliminate which causes the least amount of calculation at each step. This ordering heuristic is called min-degree ordering. It is widely used in many applications including the AMD, “\\” commands in Matlab and Julia.

# Fill graph

To understand min-degree ordering, we will view the process of Gaussian Elimination from the perspective of graphs. For any n-by-n matrix A, we can construct an n-vertex graph according to the following rule:

Connect i-th vertex to j-th vertex via an edge in G for each non-zero non-diagonal entry \\(A_{i,j}\\). 

This graph G is called the fill graph of the matrix A. Since we only focus on symmetric matrices, all fill graphs we consider are undirected graphs. Now let’s take a look at how the fill graph evolves when we run Gaussian Elimination on its associated matrix.

Without loss of generality, we consider eliminating the first variable from an n-by-n SPD matrix A. At first, we divide matrix A into following four blocks:
 ![eq10](../eq10.png)

In this expression,  is a scalar, a is an (n-1)-dimensional vector and B is an (n-1)-by-(n-1) submatrix. The first variable is associated with the first column of the matrix. Our goal is to turn vector a, at the bottom left block, into a zero column vector via basic matrix row operations.  

Mathematically, for each row \\(i>1\\) of matrix A, we will subtract it by \\((\alpha,a^T)\\), the first row of the matrix, multiplied by \\(a_i/\alpha\\). As a result, vector a will become a all-zero vector and block B will become \\(B-aa^T/\alpha\\). The new submatrix \\(B-aa^T/\alpha\\) is called the Schur complement of matrix A for block B:
  ![eq11](../eq11.png)

To compute the Schur complement efficiently, we only need to subtract from each entry \\(B_{i,j}\\) the quantity \\(a_ia_j/\alpha\\) if both \\(a_i\\) and \\(a_j\\) are non-zero, because the entry value will remain the same otherwise. In the associated fill graph, a new edge between vertex i and j will be formed only if \\(a_ia_j\\) is not zero. Notice that \\(a_i\\) is not zero if and only if the first vertex, associated with the variable to eliminate, is connected to vertex i. In other words, all the neighbors of the first vertex will become connected after the elimination. Finally, the first vertex and all its edges will be removed in the fill graph because Gaussian Elimination will be called recursively on the Schur complement, associated with the remaining part of the original fill graph.

We use the word “pivot” to describe the operations done to the vertex in the fill graph when its associated variable is eliminated from the linear system. Specifically, when we pivot a vertex from the graph, we will form a clique out of its neighbors and then remove itself and all its edges from the graph.

# Min-degree ordering

Let’s take a look at the min-degree ordering heuristic from the perspective of the graph. From the definition, the min-degree ordering heuristic always greedily chooses the variable to eliminate which does the least work at the current stage. Equivalently, it always picks the vertex in the fill graph which adds the fewest edges. Since the number edges to add is \\(O(k^2)\\), where k is the number of neighbors of the vertex to pivot, min-degree ordering heuristic always pivots the vertex with the minimum degree.
 
Thus, for the rest of this article, we focus on the question: how to find a min-degree ordering efficiently?

There exists a naive algorithm: we simply maintain the fill graph in an adjacency matrix and update it upon each pivot operation. Basically, what we do is simulating Gaussian Elimination on the fill graph except that we have to maintain the degree of each vertex and find the min-degree vertex each time. This is not useful because we have to make sure that it takes significantly less time to find the min-degree ordering as a preprocessing step than Gaussian Elimination in order to take advantage of the cache bonus during Gaussian Elimination.

Notice that the bottleneck of the naive algorithm comes down to eager update strategy upon any pivot operation. In other words, we spend most of the time on making cliques upon any pivot operation. To bypass the cost from this update strategy, we introduce an implicit representation of the fill graph.

# Implicit representation of the fill graph

In the implicit representation of the fill graph, we mark each vertex in two colors: red and green. In the original fill graph, all vertices are marked in green. Whenever we need to pivot a vertex, we will simply mark it in red, instead of adding a clique among all its neighbors and removing it from the graph. In the following example. Figure (a) shows the implicit representation of the fill graph after pivoting vertex \\(v_5\\) and \\(v_7\\) while figure (b) shows the fill graph after the same operations.
 ![eq12](../eq12.png)

We can show that any two vertices are connected by an edge in the fill graph if and only if there exists a path connecting these two vertices via only intermediate red vertices in the implicit representation of the fill graph. In the example above, \\(v_2\\) can reach \\(v_6\\) via red vertex \\(v_7\\) and \\(v_5\\) in the implicit representation of the fill graph, shown in figure (a), so \\(v_2\\) is connected with \\(v_6\\) by an edge in the fill graph, shown in figure (b).

Since connected red vertices in the implicit representation of the fill graph are working together to get one green vertex connected to the other, we can merge all connected red vertices in one red vertex without losing any connectivity information. We call the graph obtained in this way the component graph. In the example above, figure (c) indicates a component graph obtained by merging 
\\(v_7\\) and \\(v_5\\) into one single red vertex \\(x_1\\) from the implicit representation of the fill graph in figure (a).

We can show that two vertices are connected in the fill graph if and only if they can reach each other via at most one red vertex in the component graph. For any green vertex in the component graph, its neighbor set in the fill graph is the union of the neighbor sets associated with all its red neighbors in the component graph and all its own green neighbors. For example, in Figure (c), the neighbor set of \\(v_2\\) in the fill graph, shown in Figure (a), is the union of the neighbor set of \\(x_1\\) and the green neighbor set of \\(v_2\\) itself in the component graph, shown in Figure (c). 

In order to find a min-degree ordering, we need to design a data structure, on top of the component graph, which maintains all the neighbor sets and the size of the union of specific neighbor sets dynamically. Specifically, for each vertex in the component graph, we need to maintain its green neighbor set and red neighbor set at the same time. The data structure should support removing a vertex from a neighbor set, in the case of marking a green vertex as red; and also support merging two neighbor sets together, in the case of contracting two red vertices together.

# Estimate union of sets

Notice that the efficiency of the data structure comes down to how to estimate the size of the union of sets. Here we will introduce two different methods for that.

To begin with, let’s finish a classic homework problem in the statistics class:

Consider n identical independent random variables from [0,1] uniform distribution. What’s the expected value of the minimum among them?

Here is the answer:

The expected value of the minimum of n identical independent [0,1]-uniform distributed random variables is \\(1/(n+1)\\).

Notice that the expected value in the solution is a function of the number of random variables. Hence, if we can estimate the expectation precisely, we can then deduce the number of variables using the inverse of the function in the solution. This idea was first proposed by Cohn ‘97 in order to estimate the number of random variables in a model where the minimum value in sets can be quickly calculated.

Now we are going to estimate the size of the union of sets with this idea. Consider the following example in our real life:

In order to boost the turnover in a supermarket, the manager wants to find out the most popular product and adjust the sale strategy accordingly. From market research, the manager knows exactly which product is appealing to which types of the customers. For example, kitchen products are popular among females, senior citizens and middle class people. Ice cream is popular among students and middle class people. Due to the large data, it is very time consuming to list off all the customers of each type. However, the customer database maintains the minimum membership card number among customers of each type. For example, the minimum membership card number among all students is 40213 and the one for middle class people is 62342. Assume that all membership card numbers are uniformly picked between 0 and 10000000. How can the manager quickly find out the most popular product?  

Notice that the set of the customers interested in a specific product is the union of sets of customers of certain types. The minimum membership card number in a union of sets is just the minimum among the minimum membership card numbers of sets of those types. In the example above, the minimum membership card number of customers interested in ice cream is 40213, which can simply be calculated by the minimum between 40213 and 62342, associated with students and middle class people respectively. Since all membership card numbers are uniformly picked between 0 and 10000000, 40213/10000000 is just a realization of a random variable centered at 1/(k+1) where k is the number of customers interested in ice cream. By calculating 1/(k+1)=40213/10000000, we get k=247.67 as an approximated estimation on the number of customers interested in ice cream.

In order to get a precise estimation, the manager needs to have several independent random variables which serve the same purpose as the membership card numbers. For instance, if each customer had three independent numbers from their membership card, driver license and passport, each of which was sampled from a uniform distributed presumably, the manager can get three independent estimates on the same random variable centered at 1/(k+1) where k is the number of customers interested in a specific product. Hence, the average of these three estimates would give a more precise evaluation on k. Specifically, in order to get the evaluation within \\(\epsilon\\) error, each customer should have \\(O(\epsilon^{-2})\\) independent sampled numbers. 

# Idea 1: the minimum of random variables

Now let’s apply this idea to the component graph. To begin with, for each vertex in the component graph, we sample a random variable uniformly distributed between 0 and 1. In order to calculate the fill degree for each vertex u, we just need to know the expected minimum among all random variables sampled by the neighbors of vertex u in the fill graph. As we know, the neighbor set of each vertex u in the fill graph is the union of the green neighbor sets in the component graph, each of which is associated with either a red neighbor of vertex u or just vertex u itself. Hence, we just need to maintain the minimum sampled value in each green neighbor set, and then calculate the minimum of those minimum values of the associated neighbor sets.

Notice that the supermarket example is just a special case of the component graph. Imagine that each green vertex in a component graph is a customer and each red vertex is associated with the customer type such as student. Whenever we want to estimate the fill degree of a green vertex, we can view that green vertex as a product, in which all customers of types associated with the red neighboring vertices are interested, and then ask how many customers are interested in that product. The vertex choice of min-degree ordering heuristic at each step is associated with the least popular product in the supermarket example. 

In fact, this idea has been widely applied in many applications such as MinHash, a technique for estimating the similarity of two sets quickly in data mining. However, in order to get a precise estimation on the set size, we need to have estimation error 1/n. Hence, we need to have \\(O(n^2)\\) duplicates of the data structure, which makes the overall time complexity even worse.

# Idea 2: coupon collector problem


So we introduce another idea to estimate the size of the union of sets precisely. The idea comes from the famous coupon collector problem:

How many coupons do you need to collect to get each one of n distinct coupons at least one? Assume that the coupon of any type is collected with exactly 1/n chance every time.

The answer is \\(O(n \ln n)\\). At a high level, one way to estimate the size of the neighbor set of a specific vertex in the graph is to have a data structure which can uniformly sample the neighbor node for each vertex. With such a data structure, we just need to have \\(O(n \log n)\\) samples to cover the entire neighbor set for each vertex. 

The trick of uniformly sampling a random neighboring vertex for each vertex is to use the minimizer as the choice of the sampler. More specifically, if we sample a real number between 0 and 1 for each vertex, each vertex will have the same chance of becoming the minimum sampled value in any fixed subset. In this case, we can construct a data structure tracking which value is generated by which vertex originally. Therefore, each vertex in the fill graph just needs to maintain the minimum value among all its fill neighbors and we use the vertex which generated that minimum value as the sampling result.   

Now we will implement a data structure on the component graph to calculate the min-degree ordering. Throughout the entire process, each vertex u in the component graph maintains three different “min-values”: x-value \\(x_u\\), y-value \\(y_u\\) and z-value \\(z_u\\).

To begin with, for each green vertex u, we sample its x-value \\(x_u\\) from a uniform distribution between 0 and 1. For each green or red vertex v, we maintain its y-value \\(y_v\\) as the minimum of the x-values of all its green neighbors. Mathematically, 
 ![eq13](../eq13.png)

For each green vertex w, we maintain its z-value \\(z_w\\) as the minimum of the y-values of all its red neighbors. Mathematically, 
 ![eq14](../eq14.png)

It is easy to verify that, for each green vertex u in the component graph, the minimum between its y-value \\(y_u\\) and z-value \\(z_u\\) is the minimum of the x-values of all its neighbors in the associated fill graph.

Notice that these x-values, y-values and z-values are computed in a three-layer structure. The x-values are sampled at the bottom layer; each y-value and each z-value is the minimum of a set of values from one layer lower.

Whenever we pivot a green vertex u, we just need to mark it in red. There will be two consequences. One is that vertex u is no longer a green neighbor of its previous neighbors. The other one is that we have to contract all newly connected red vertices. The time analysis on these two consequences are similar and we will only talk about the first one in this post.

It seems that the change of the color may trigger a huge chain effect from the first consequence. For example, dyeing vertex u with red will make it no longer the green neighbor of other vertices. Hence, all its neighbors may get their y-value changed, which may further cause the update of all the z-values of its neighbor’s neighbors.

In fact, this is not always the case. When we color vertex u red, we only need to update the y-values of some of its neighbors. This is because when we remove a number from the set, the minimum number of the set may change only if the minimum number is exactly the removed number. When we color vertex u in red, for each of its neighbor v, the recalculation on the y-value \\(y_v\\) is only required with only 1/k probability, where k is the degree of vertex v. This is because vertex u has only 1/k chance of having its sampled x-value \\(x_u\\) as the minimum value among all k neighbors of vertex v. 

Since the recalculation on the y-value takes \\(O(k)\\) time, by simply enumerating associated x-values of all its k neighbors, it takes constant expected time to update the y-value of a vertex caused by the change of the color of each one of its neighbors. Similarly, we can show that it takes constant expected time to update the z-value of any vertex with respect to the change of the y-value of each one of its neighbors. In conclusion, the expected update time on either y-value or z-value is constant per edge in the component graph. 

Hence, the overall running time from the first consequence of the pivot operation is \\(O(m)\\) where m is the number of edges in the graph. With the similar time analysis, the overall running time for the second consequence is \\(O(m\log n)\\). Notice that the extra \\(O(\log n)\\) factor comes from the overhead cost of melding two neighbor sets when we contract two newly-connected red vertices together.

Now we have a data structure which, for each vertex, maintains the minimum x-value of all its fill neighbors dynamically. At the same time, we maintain a hash table tracking which value is the same as the x-value sampled by which vertex at the beginning. Combining the data structure and this hash table together, we have a uniform vertex sampler which chooses a random fill neighbor uniformly for each vertex. 

As we learned from coupon collector problem, for each vertex, we need to have \\(O(n \log n)\\) such samplers to cover its entire neighbor sets in the fill graph with a high probability. At a high level, we need to sample a k-dimensional x-vector uniformly from a k-dimensional hypercube \\([0,1]^k\\) for each vertex at the beginning, where \\(k=O(n \log n)\\). For each dimension, we maintain a uniform vertex sampler for each vertex. With all these uniform vertex samplers, we can maintain the fill neighbor set for each vertex dynamically and generate the min-degree ordering in \\(O(mn \log^2n)\\) time.

Theoretically, the time complexity of this min-degree algorithm is smaller than the naive algorithm. It is significantly faster than the naive algorithm when the fill graph is sparse enough. For instance, when the number of edges of the fill graph is \\(O(n)\\), the running time of the min-degree algorithm is \\(O(n^2 \log^2 n)\\), while the naive algorithm runs in \\(O(n^3)\\) time.

# Summary

In this post, we talked about how to solve linear systems using Gaussian Elimination. From the perspective of the graph, we associate the process of Gaussian Elimination with the pivot ordering in graphs. Then we introduced the min-degree heuristic as a greedy strategy on the selection of the vertex to pivot. To compute the min-degree ordering efficiently, we talked about two different methods for estimating the size of the union of sets. With the method inspired by the coupon collector problem, we constructed a data structure which quickly measures the vertex degree in the fill graph. Finally, we designed an algorithm which computes the min-degree ordering efficiently.


