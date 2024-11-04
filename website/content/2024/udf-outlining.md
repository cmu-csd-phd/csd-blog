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

SQL is the de facto query language used to interact with databases. Since SQL is declarative, users express the intended result of their query rather than the concrete procedural steps to produce the answer. Database management systems (DBMSs) find fast execution strategies for SQL queries using a component called the query optimizer. The optimizer’s task is to search the space of equivalent query plans  (specific procedural strategies to retrieve the result of a query) and select the plan with the lowest estimated runtime cost. After decades of research on query optimization, database systems have become remarkably effective at optimizing SQL queries.

![Figure 1: Query Optimizer.](optimizer.png)
<p style="text-align: left;">
<b>Figure 1, The Query Optimizer:</b>
<em>
The query optimizer takes a SQL query as input and produces a query plan (a concrete execution strategy to evaluate the query) as output. The query optimizer aims to select the query plan with the lowest estimated cost. It achieves this by enumerating the space of equivalent query plans (the plan space) and using a cost model to estimate the runtime cost of each candidate plan.
</em></p>

# User-Defined Functions (UDFs)

Although most database queries are written purely in SQL, billions of queries per day make calls to User-Defined Functions (UDFs), procedural functions written in non-SQL programming languages such as Python or PL/SQL. 

![Figure 2: UDF Example.](udf.png)
<p style="text-align: left;">
<b>Figure 2, An Example UDF:</b>
<em>
An example UDF written in PL/SQL. The function <b>is_vip</b>
takes a customer key as input and returns whether the customer is a VIP.
A customer is a VIP if the total amount spent 
on orders (computed using the <b>SELECT</b> statement) exceeds 1,000,000.
</em></p>

Figure 2 showcases an example PL/SQL UDF, <b>is_vip</b>, which 
returns whether a customer is a VIP. The <b>is_vip</b> UDF mixes declarative code
(the <b>SELECT</b> statement) and procedural code (<b>IF/ELSE</b> statements). Allowing
users to mix procedural and declarative code provides a more convenient and intuitive way to express query logic than pure SQL. As a result, UDFs provide significant software engineering benefits to database users, namely the ability to reuse code, express query logic more concisely, and decompose complex queries into modular functions.

# Row-By-Agonizing-Row (RBAR) Execution

![Figure 3: Row-By-Agonizing-Row (RBAR) Execution of Queries with UDFs.](rbar.png)
<p style="text-align: left;">
<b>Figure 3, Row-By-Agonizing-Row (RBAR) Execution of Queries with UDFs:</b>
<em>
An example query which invokes the <b>is_vip</b> UDF from Figure 2. The DBMS naively evaluates the UDF for each input row of the <b>customer</b> table. Each UDF call executes an embedded <b>SELECT</b> statement that scans the <b>orders</b> table. As a result, the complexity of the query is <b>Θ(|customer| × |orders|)</b>, which is unreasonably slow to execute. As a result, users in the database community have collectively described UDF execution as RBAR (Row-By-Agonizing-Row).
</em></p>

Unfortunately, UDFs come with a performance cost. Unlike SQL, which is purely declarative, UDFs mix declarative and procedural programming paradigms,
making them opaque to the query optimizer. As a result, the DBMS must execute
UDFs in a naive "row-by-row" fashion, where the UDF is reinvoked for each input row.
In the process, <b>SELECT</b> statements embedded inside the UDF are re-evaluated
for each row, dramatically slowing down query execution. Database practitioners have
termed this naive, inefficient, row-by-row execution of UDFs as RBAR (Row-By-Agonizing-Row).

Figure 3 showcases an example query invoking the <b>is_vip</b> UDF from Figure 2.
The DBMS invokes the UDF RBAR, calling the UDF for each row of the <b>customer</b> table.
With each call to the UDF, the DBMS executes the embedded <b>SELECT</b> statement, re-scanning the <b>orders</b> table and leading to extremely inefficient query execution.

# UDF Inlining (Intuition)

![Figure 4: UDF Inlining Intuition.](intuition.png)
<p style="text-align: left;">
<b>Figure 4, UDF Inlining Intuition:</b>
<em>
The key intuition behind UDF inlining is to translate UDFs from opaque functions into SQL subqueries, a declarative representation that the DBMS can optimize effectively. In the above example, inlining replaces the <b>is_vip</b> UDF by an equivalent SQL subquery.
</em></p>

RBAR execution of UDFs arises because UDFs are opaque functions written in a 
non-declarative paradigm that the DBMS cannot effectively reason about. Such row-by-row
execution is reminiscent of how database systems logically evaluate SQL subqueries, 
whereby the DBMS re-evaluates a subquery for each row of the calling query. The key 
distinction, however, between UDFs and subqueries is that the database community has 
spent decades optimizing subqueries. Hence, if the DBMS can translate a UDF into an 
equivalent SQL subquery, the query is left entirely in SQL, which is amenable to 
effective query optimization. Translating UDFs to equivalent SQL subqueries is\
known as <b>UDF inlining</b>, and enables the efficient execution of queries containing UDFs.

# Subquery Unnesting

![Figure 5: Subquery Unnesting.](subquery.png)
<p style="text-align: left;">
<b>Figure 5, Subquery Unnesting:</b>
<em>
An illustration of how DBMSs perform subquery unnesting. The SQL query is rewritten from
an inefficient query containing a subquery to an equivalent query containing joins that are significantly faster to execute.
</em></p>

The database research community has spent decades developing optimization techniques to 
evaluate SQL queries with subqueries efficiently. Subquery unnesting is performed by the 
DBMS's query optimizer, replacing subqueries with equivalent join operators.

On the left-hand side of Figure 5 is a SQL query containing a subquery (shown in red).
The naive way of evaluating the query is by re-evaluating the subquery for each row of 
the <b>orders</b> table and rescanning the <b>customer</b> table. Evaluating the query in
this manner results in a runtime of <b>Θ(|customer| × |orders|)</b>, which is extremely inefficient.

Instead of evaluating subqueries in a naive "row-by-row" manner, database systems perform subquery unnesting.
Subquery unnesting replaces the subquery with equivalent join operators. The right-hand side of Figure 5 illustrates the rewritten query,
which the DBMS evaluates efficiently in <b>Θ(|customer| + |orders|)</b> time with hash joins.

# UDF Inlining

![Figure 6: UDF Inlining.](inlining.png)
<p style="text-align: left;">
<b>Figure 6, UDF Inlining:</b>
<em>
An illustration of the UDF inlining technique for our motivating example.
Inlining translates the <b>is_vip</b> UDF into an equivalent SQL subquery with <b>LATERAL</b> joins. 
The generated subquery is then "inlined" into the calling query.
After inlining, the query is represented entirely in SQL, which the DBMS can optimize 
effectively.
</em></p>

UDF inlining translates UDFs into equivalent SQL subqueries in three key steps. First,
inlining translates a UDF's statements to SQL tables. <b>IF/ELSE</b> blocks become 
<b>CASE WHEN</b> statements, assignments (i.e., <b>x = y</b>) become projections (i.e., <b>SELECT y AS x</b>).
Then, the DBMS chains together these statements with <b>LATERAL</b> joins, creating a
 single SQL expression that is equivalent to the original UDF. The last step is to 
 "inline" the generated SQL expression into the calling query, eliminating the UDF call.
  After applying UDF inlining, queries are represented in pure SQL, automatically
improving the performance of queries with UDFs by multiple orders of magnitude.

# The Problem with UDF Inlining


![Figure 7: UDF Inlining = Complex Queries.](skull.png)
<p style="text-align: left;">
<b>Figure 7, UDF Inlining = Complex Queries:</b>
<em>
The complex query produced by UDF inlining. Most DBMSs cannot unnest the generated subquery,
falling back to slow, inefficient RBAR execution.
</em></p>

Unfortunately, UDF inlining is ineffective for most real-world queries because it produces large, complex SQL queries that are hard to optimize. In particular, to achieve significant performance improvements with UDF inlining, the DBMS must unnest the generated subquery. Yet, UDF inlining produces complex subqueries containing <b>LATERAL</b> joins that most DBMSs fail to unnest. As a result, the DBMS evaluates the subquery naively for each row, akin to the RBAR execution strategy used before applying UDF inlining.

![Figure 8: Subquery Unnesting (ProcBench).](cant-unnest.png)
<p style="text-align: left;">
<b>Figure 8, Subquery Unnesting (ProcBench):</b>
<em>
A table indicating whether a given DBMS (SQL Server or DuckDB) successfully unnested a UDF-centric
query from the Microsoft SQL ProcBench. A green tick indicates that the unnesting succeeded. A grey cross
 indicates that the unnesting failed.
</em></p>

To understand how effectively DBMSs optimize queries with UDFs, we ran the Microsoft 
SQL ProcBench, a UDF-centric benchmark containing 15 queries 
modeled after real-world customer queries. We evaluated these queries on two DBMSs:
Microsoft SQL Server and DuckDB. A query executes efficiently only if the DBMS can 
unnest the subquery generated by UDF inlining otherwise the DBMS evaluates it RBAR. 
SQL Server unnests only 4 out of 15 of the queries after inlining. Alternatively stated,
SQL Server evaluates 11 out of 15 of the ProcBench queries RBAR, with underwhelming 
performance. Hence, for most real-world UDF-centric queries, inlining is
ineffective on SQL Server. Although DuckDB supports arbitrary unnesting of subqueries and achieves
high performance on all 15 queries, only a handful of DBMSs implement this technique,
and integrating it into existing systems is highly challenging. Hence,
for the majority of UDF-centric queries, inlining is not effective for the vast majority of DBMSs.

# Our Solution: UDF Outlining

Fundamentally, we observe that inlining <b>entire UDFs</b> generates complex subqueries that are challenging for the DBMS
to unnest. Instead of inlining entire UDFs, a better approach is to analyze the UDF, deconstruct it into smaller pieces, and 
inline only the  pieces that help query optimization. To achieve this, we propose <b>UDF outlining</b>, an optimization technique 
that extracts UDF code fragments into separate functions that are intentionally not inlined, minimizing UDF code complexity. 
We implement UDF outlining in conjunction with four other complementary UDF-centric optimizations in <b>PRISM</b>, our optimizing compiler for UDFs.    

![Figure 9: PRISM.](prism.png)
<p style="text-align: left;">
<b>Figure 9, PRISM:</b>
<em>
PRISM is an optimizing compiler for UDFs, deconstructing a UDF into separate inlined and outlined pieces. By operating on
UDF pieces, only the code helpful for query optimization is exposed to the DBMS, intentionally leaving the remaining code opaque through UDF outlining. PRISM is reminiscent of a prism of light, breaking a UDF down into its constituent pieces.
</em></p>

PRISM is an acronym for the five UDF-centric optimizations that it supports:
1. <b>P</b>redicate Hoisting
2. <b>R</b>egion-Based UDF Outlining
3. <b>I</b>nstruction Elimination
4. <b>S</b>ubquery Elision
5. Query <b>M</b>otion

To illustrate PRISM's optimizations, we will apply its three relevant optimizations to our motivating example.

# Region-Based UDF Outlining

![Figure 10: Region-Based UDF Outlining.](outlining.png)
<p style="text-align: left;">
<b>Figure 10, Region-Based UDF Outlining:</b>
<em>Instead of inlining the entire UDF, PRISM extracts the largest regions of non-<b>SELECT</b> code into separate outlined functions. In our example,
PRISM extracts the <b>IF/ELSE</b> block and <b>RETURN</b> statement into an outlined function <b>f(...)</b>, which is opaque to the query optimizer.
</em></p>

The first and most critical optimization that PRISM performs is region-based UDF outlining. The goal of UDF outlining is to extract the largest blocks of unhelpful code 
for query optimization into separate functions that are opaque to the DBMS. PRISM achieves this by representing a UDF as a hierarchy of program <b>regions</b>,
where each region is eligible for outlining. PRISM identifies the largest regions of UDF code that do not contain any <b>SELECT</b> statements and extracts each
region into a separate outlined function. PRISM then compiles the outlined functions to machine code, preventing the inlining of that region. Lastly, PRISM replaces the
region in the original UDF with an opaque function call into the outlined function, simplifying the UDF substantially.

Figure 10 illustrates how PRISM applies region-based UDF outlining to our motivating example. First, PRISM identifies the region containing the <b>IF/ELSE</b> block and <b>RETURN</b> statement as the largest region not containing <b>SELECT</b> statements. Next, it extracts the region into a new outlined function <b>f(...)</b>, compiles it to machine code,
and replaces the original region with an opaque function call to the outlined function. Through UDF outlining, PRISM significantly simplifies the UDF,
 enabling more effective query optimization.

# Instruction Elimination

![Figure 11: Instruction Elimination.](instruction.png)
<p style="text-align: left;">
<b>Figure 11, Instruction Elimination:</b> After UDF outlining, PRISM applies instruction elimination to remove as many UDF instructions as possible, reducing 
the number of <b>LATERAL</b> joins from inlining. Instruction elimination replaces the uses of a variable with its definitions. In our example,
PRISM eliminates the definition of <b>total</b>, directly forwarding its definition to the use by <b>f(...)</b>.
<em>
</em></p>

# Subquery Elision

![Figure 12: Subquery Elision.](elision.png)
<p style="text-align: left;">
<b>Figure 12, Subquery Elision:</b>
<em>In our example, PRISM reduces the UDF to a single <b>RETURN</b> statement after instruction elimination. When a UDF consists of a single <b>RETURN</b> statement,
 PRISM performs subquery elision and injects the return value into the calling query rather than substituting it as a SQL subquery.
</em></p>

# Experimental Setup

# Experiments (Unnesting)

![Figure 13: Subquery Unnesting (ProcBench).](unnest.png)
<p style="text-align: left;">
<b>Figure 13, Subquery Unnesting (ProcBench):</b>
<em>
When inlining entire UDFs, SQL Server unnests only 4 out of 15 queries in the
Microsoft SQL ProcBench. After optimizing the UDF, PRISM hides the irrelevant
pieces of the UDF through outlining, only exposing the relevant pieces of the
UDF to the query optimizer. As a consequence, queries become significantly simpler,
and SQL Server can unnest 12 out of 15 queries in the benchmark. DuckDB can
unnest arbitrary subqueries, with the DBMS unnesting all 15 queries with both approaches.
</em></p>

# Experiments (Overall Speedup)

![Figure 14: Overall Speedup (ProcBench).](speedup.png)
<p style="text-align: left;">
<b>Figure 14, Overall Speedup (ProcBench):</b>
<em>
To understand the performance improvement of PRISM, compared to inlining the entire UDF,
we report the overall speedup when running queries with PRISM toggled. Speedup is calculated by dividing the runtime of running a given query without PRISM (i.e., inlining the entire UDF) by the runtime with PRISM. We report the average speedup (excluding outliers), and the maximum speedup (including outliers). We observe that PRISM provides significant performance improvements over existing UDF optimization techniques.
</em></p>

# Conclusion