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

SQL is the defacto query language for interacting with databases. Since SQL is declarative, users express the intended result of their query rather than the concrete procedural steps to produce the query result. Database management systems (DBMSs) find fast execution strategies for SQL queries using a component called the query optimizer. The optimizer's task is to search the space of equivalent query plans (specific procedural strategies to retrieve the result of a query) and select the plan with the lowest estimated runtime cost. After decades of research on query optimization, database systems have become remarkably effective at optimizing SQL queries.

![Figure 1: Query Optimizer.](optimizer.png)
<p style="text-align: left;">
<b>Figure 1, The Query Optimizer:</b>
<em>
The query optimizer takes a SQL query as input and produces a query plan
 (a concrete execution strategy to evaluate the query) as output. The goal of the query optimizer is to select the query plan with the lowest estimated cost. It achieves this by enumerating the space of equivalent query plans (the plan space) and uses a cost model to estimate the runtime cost of each candidate plan.
</em></p>

# User-Defined Functions (UDFs)

Although most database queries are written purely in SQL, billions of queries per day make calls to User-Defined Functions (UDFs), procedural functions written in non-SQL programming languages such as Python or PL/SQL. 

![Figure 2: UDF Example.](udf.png)
<p style="text-align: left;">
<b>Figure 2, An Example UDF:</b>
<em>
An example UDF written in PL/SQL. The function <b>is_vip</b>
takes a customer key as input and returns whether the customer is a VIP.
A customer is a VIP if the total amount of money spent 
on orders (computed using the <b>SELECT</b> statement) exceeds 1,000,000.
</em></p>

Figure 2 showcases an example PL/SQL UDF, <b>is_vip</b>, which 
returns whether a customer is a VIP. The <b>is_vip</b> UDF mixes declarative code
(the <b>SELECT</b> statement) and procedural code (<b>IF/ELSE</b> statements). Allowing
users to mix procedural and declarative code provides a more convenient and intuitive means to express query logic compared to pure SQL. As a result, UDFs provide significant software engineering benefits to database users, namely the ability to reuse code, express query logic more concisely, and decompose complex queries into modular functions.

# Row-By-Agonizing-Row (RBAR) Execution

![Figure 3: Row-By-Agonizing-Row (RBAR) Execution of Queries with UDFs.](rbar.png)
<p style="text-align: left;">
<b>Figure 3, Row-By-Agonizing-Row (RBAR) Execution of Queries with UDFs:</b>
<em>
An example query which invokes the <b>is_vip</b> UDF from Figure 2. The DBMS naively evaluates the UDF for each input row of the <b>customer</b> table. Each UDF call executes an embedded <b>SELECT</b> statement that scans the <b>orders</b> table. As a result, the complexity of the query is <b>Θ(|customer| × |orders|)</b>, which is unreasonably slow to execute. As a result, users in the database community, have collectively described UDF execution as RBAR (Row-By-Agonizing-Row).
</em></p>

Unfortunately, UDFs come with a performance cost. Unlike SQL, which is purely declarative, UDFs mix declarative and procedural programming paradigms,
making them opaque to the query optimizer. As a result, the DBMS must execute
UDFs in a naive "row-by-row" fashion, where the UDF is reinvoked for each input row.
In the process, <b>SELECT</b> statements embedded inside the UDF are re-evaluated
for each row, dramatically slowing down query execution. Database practitioners have
termed this naive, inefficient, row-by-row execution of UDFs as RBAR (Row-By-Agonizing-Row).

Figure 3 showcases an example query invoking the <b>is_vip</b> UDF from Figure 2. The
UDF is evaluated RBAR, where for each row of the <b>customer</b> table, the UDF is called. With each call to the UDF, the embedded <b>SELECT</b> statement is executed, re-scanning the <b>orders</b> table and leading to extremely inefficient, RBAR, query execution.

# UDF Inlining (Intuition)

![Figure 4: UDF Inlining Intuition.](intuition.png)
<p style="text-align: left;">
<b>Figure 4, UDF Inlining Intuition:</b>
<em>
The underwhelming performance of UDFs arises because they are opaque, non-declarative 
functions that the DBMS cannot reason about it, leading to RBAR execution. 
Another SQL language feature, SQL subqueries, also execute RBAR, where for each row of the outer query, the subquery is re-evaluated. However, the key distinction between UDFs and subqueries, is that the database community has spent decades optimizing subqueries. Hence, if a UDF can be translated into an equivalent SQL subquery, the UDF call can be replaced by  the subquery, leaving the query entirely in SQL, in a form that is amenable to effective query optimization. Translating UDFs to SQL subqueries is the key intuition behind UDF inlining.
</em></p>

# Subquery Unnesting

![Figure 5: Subquery Unnesting.](subquery.png)
<p style="text-align: left;">
<b>Figure 5, Subquery Unnesting:</b>
<em>
The database research community has spent decades developed optimization techniques, to efficiently evaluate SQL queries with subqueries. Subquery unnesting is performed by the DBMSs query optimizer and rewrites the query to replace the subquery with equivalent join operators. On the left hand side, the SQL query evaluates a subquery (shown in red)
for each row of the <b>orders</b> table, which will rescan the <b>customer</b> table,
each time the UDF is invoked, resulting in a runtime of <b>Θ(|customer| × |orders|)</b>. However, after the DBMS performs subquery unnesting,
the query is rewritten as shown on the right hand side. The DBMS replaced the subquery
with a join, enabling the rewritten query to be evaluated efficiently in <b>Θ(|customer| + |orders|)</b> with hash joins.</em></p>

# UDF Inlining

![Figure 6: UDF Inlining.](inlining.png)
<p style="text-align: left;">
<b>Figure 6, UDF Inlining:</b>
<em>
UDF inlining automatically removes all UDF calls by replacing
them with equivalent SQL subqueries. Inlining
leaves queries entirely in SQL which the query optimizer can effectively reason about. As a result, UDF inlining can improve the performance of UDF-centric queries
by multiple orders of magnitude.
</em></p>

# The Problem with UDF Inlining

![Figure 7: Subquery Unnesting (ProcBench).](cant-unnest.png)
<p style="text-align: left;">
<b>Figure 7, Subquery Unnesting (ProcBench):</b>
<em>
To achieve significant performance improvements with UDF inlining, the generated 
subquery must be unnested by the DBMS. To understand how often this occurs, we
ran the Microsoft SQL ProcBench, a UDF-centric benchmark containing 15 queries 
modelled after real-world customer queries. On SQL Server, only 4 out of 15 of the 
queries could be unnested after inlining. Therefore, 11 out of 15 of the ProcBench
 queries have underwhelming performance (RBAR). DuckDB supports arbitrary unnesting
  and can unnest all 15 queries after inlining.
</em></p>

# Our Solution: UDF Outlining

![Figure 8: PRISM.](prism.png)
<p style="text-align: left;">
<b>Figure 8, PRISM:</b>
<em>
</em></p>

![Figure 9: Region-Based UDF Outlining.](outlining.png)
<p style="text-align: left;">
<b>Figure 9, Region-Based UDF Outlining:</b>
<em>
</em></p>

![Figure 10: Instruction Elimination.](instruction.png)
<p style="text-align: left;">
<b>Figure 10, Instruction Elimination:</b>
<em>
</em></p>

![Figure 11: Subquery Elision.](elision.png)
<p style="text-align: left;">
<b>Figure 11, Subquery Elision:</b>
<em>
</em></p>

# Experimental Setup

# Experiments (Unnesting)

![Figure 12: Subquery Unnesting (ProcBench).](unnest.png)
<p style="text-align: left;">
<b>Figure 12, Subquery Unnesting (ProcBench):</b>
<em>
When inlining entire UDFs, SQL Server unnests only 4 out of 15 queries in the
Microsoft SQL ProcBench. After optimizing the UDF, PRISM hides the irrelevant
pieces of the UDF through outlining, only exposing the relevant pieces of the
UDF to the query optimizer. As a consequence, queries become significantly simpler,
and SQL Server can unnest 12 out of 15 queries in the benchmark. DuckDB can
unnest arbitrary subqueries, with the DBMS unnesting all 15 queries with both approaches.
</em></p>

# Experiments (Overall Speedup)

![Figure 13: Overall Speedup (ProcBench).](speedup.png)
<p style="text-align: left;">
<b>Figure 13, Overall Speedup (ProcBench):</b>
<em>
To understand the performance improvement of PRISM, compared to inlining the entire UDF,
we report the overall speedup when running queries with PRISM toggled. Speedup is calculated by dividing the runtime of running a given query without PRISM (i.e., inlining the entire UDF) by the runtime with PRISM. We report the average speedup (excluding outliers), and the maximum speedup (including outliers). We observe that PRISM provides significant performance improvements over existing UDF optimization techniques.
</em></p>

# Conclusion