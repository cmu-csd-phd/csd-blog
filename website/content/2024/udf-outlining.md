+++
title = "The Key to Effective UDF Optimization: Before Inlining, First Perform Outlining"
date = 2024-08-10

[taxonomies]
areas = ["Systems"]
tags = ["database systems", "compiler optimization", "query optimization", "query languages"]

[extra]
author = {name = "Sam Arch", url = "www.samarch.xyz" }
committee = [
    {name = "Wan Shen Lim", url = "https://wanshenl.me/"},
    {name = "Phillip Gibbons", url = "https://www.cs.cmu.edu/~gibbons/"},
    {name = "Dimitrios Skarlatos", url = "https://www.cs.cmu.edu/~dskarlat/"}
]
+++

# Background

SQL is the defacto query language for interacting with database systems. Since SQL is a declarative programming language, users express the intended result of their query rather than the concrete procedural steps to produce the query result. Database systems execute SQL efficiently by using a component called the query optimizer. The optimizer's task is to search the space of equivalent query plans (specific procedural strategies to retrieve the result of a query) for a given SQL query and select the plan with the lowest estimated cost. After decades of research on query optimization, database systems have become remarkably good at executing SQL queries efficiently.

![Figure 1: Query Optimizer.](optimizer.png)
<p style="text-align: left;">
<b>Figure 1, The Query Optimizer:</b>
<em>
The query optimizer takes a SQL query as input and produces a query plan
 (a concrete execution strategy to evaluate the query) as output. The goal of the query optimizer is to select the fastest executing query plan. It achieves this by enumerating the space of equivalent query plans (the plan space) and using a cost model to estimate the runtime cost of each candidate plan.
</em></p>

# User-Defined Functions (UDFs)

Billions of SQL queries per day make calls to User-Defined Functions (UDFs) which are procedural functions written in non-SQL programming languages such as Python or PL/SQL. Since UDFs are procedural (non-declarative) functions, they are opaque and the query optimizer cannot reason about them, leading to slow, inefficient query plans.

![Figure 2: UDF Example.](udf.png)
<p style="text-align: left;">
<b>Figure 2, An Example UDF:</b>
<em>
An example UDF written in PL/SQL. The function <b>is_vip</b>
takes a customer key as input and returns whether the customer is a VIP.
A customer is a VIP if the total amount of money spent 
on orders (computed using the <b>SELECT</b> statement) exceeds 1,000,000.
</em></p>

# Row-By-Agonizing-Row (RBAR) Execution

![Figure 3: UDF Example.](rbar.png)
<p style="text-align: left;">
<b>Figure 3, Row-By-Agonizing-Row (RBAR) Execution of UDFs:</b>
<em>
UDFs are opaque functions written in a non-declarative paradigm that 
the query optimizer cannot reason about effectively.
As a result, the DBMS executes UDFs Row-By-Agonizing-Row (RBAR), invoking the 
UDF for every row of the outer query. In our example, the <b>is_vip</b> UDF
is invoked for each row of the <b>customer</b> table. Each time the UDF is invoked, 
the embedded <b>SELECT</b> statement is executed, which scans every row of the
<b>orders</b> table. As a result, the complexity of the query is <b>Θ(|customer|×|order|)</b>, which is unreasonably slow to execute. 
</em></p>

# UDF Inlining (Intuition)

![Figure 4: UDF Inlining Intuition.](intuition.png)
<p style="text-align: left;">
<b>Figure 4, UDF Inlining Intuition:</b>
<em>
The underwhelming performance of UDFs arises because they are opaque, non-SQL 
functions that the DBMS must call RBAR. Another SQL construct, SQL subqueries, are
logically executed RBAR, where for each row of the outer query, the subquery is evaluated. However, the key distinction between UDF calls and subqueries, is that the database community has spent decades optimizing subqueries. Hence, if a UDF can be translated into an equivalent SQL subquery, the UDF call can be replaced by 
the subquery, leaving the query entirely in SQL, in a form that is amenable to 
effective query optimization. Translating UDFs to SQL subqueries is the key intuition behind UDF inlining.
</em></p>

# Subquery Unnesting

# UDF Inlining

![Figure 4: UDF Inlining.](inlining.png)
<p style="text-align: left;">
<b>Figure 4, UDF Inlining:</b>
<em>
UDF inlining automatically removes all UDF calls by replacing
them with equivalent SQL subqueries. Inlining
leaves queries entirely in SQL which the query optimizer can effectively reason about. As a result, UDF inlining can improve the performance of UDF-centric queries
by multiple orders of magnitude.
</em></p>

# The Problem with UDF Inlining

Unnesting Table

# Our Solution: UDF Outlining

PRISM Diagram

Outlining

Instruction Elimination

Subquery Elision

# Experiments

Unnesting

Overall Speedup

# Conclusion