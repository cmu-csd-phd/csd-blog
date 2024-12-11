+++
title = "The Key to Effective UDF Optimization: Before Inlining, First Perform Outlining"
date = 2024-12-12

[taxonomies]
areas = ["Systems"]
tags = ["database systems", "compiler optimization", "query optimization", "query languages"]

[extra]
author = {name = "Sam Arch", url = "https://www.cs.cmu.edu/~sarch/" }
committee = [
    {name = "Wan Shen Lim", url = "https://wanshenl.me/"},
    {name = "Phillip Gibbons", url = "https://www.cs.cmu.edu/~gibbons/"},
    {name = "Jonathan Aldrich", url = "https://www.cs.cmu.edu/~aldrich/"}
]
+++

# Background

SQL is the de facto query language used to interact with databases. Since SQL is declarative, users express the <b>intended result</b> of their query rather than the concrete procedural steps to produce the answer. Database management systems (DBMSs) find fast execution strategies for SQL queries using a component called the [query optimizer](https://www.vldb.org/pvldb/vol9/p204-leis.pdf) (shown in Figure 1). The optimizer’s task is to search the space of equivalent query plans  (specific procedural strategies to retrieve the query result), estimate the number of rows produced by each operator (cardinalities), and select the plan with the lowest estimated runtime cost. After decades of research on query optimization, database systems have become remarkably effective at optimizing SQL queries.

<img src="optimizer.png" alt="Figure 1: Query Optimizer." width="70%" />
<p style="text-align: left;">
<b>Figure 1, The Query Optimizer:</b>
<em>
The query optimizer takes a SQL query (<b>SELECT ...</b>) as input and produces a query plan (shown on the right-hand side) as output. The query optimizer aims to select the query plan with the lowest estimated cost. It achieves this by enumerating the space of equivalent query plans (the plan space), estimating each operator's cardinalities, and estimating each candidate plan's runtime cost.
</em></p>

# User-Defined Functions (UDFs)

Although most database queries are written purely in SQL, [billions of queries per day make calls to User-Defined Functions (UDFs)](https://www.vldb.org/pvldb/vol11/p432-ramachandra.pdf), procedural functions written in non-SQL programming languages such as Python or PL/SQL. 

<img src="rbar.png" alt="Figure 2: An example query invoking a PL/SQL UDF." width="70%" />
<p style="text-align: left;">
<b>Figure 2, An example query invoking a PL/SQL UDF:</b>
<em>
The query computes for each <b>customer</b>, their name, and whether they are a VIP.
</em></p>

<img src="udf.png" alt="Figure 3: UDF Example." width="70%" />
<p style="text-align: left;">
<b>Figure 3, An Example UDF:</b>
<em>
An example UDF written in PL/SQL. The function <b>is_vip</b>
takes a customer key as input and returns whether the customer is a VIP.
A customer is a VIP if the total amount spent 
on their orders (computed using the <b>SELECT</b> statement) exceeds 1,000,000.
</em></p>

Figure 2 showcases an example query invoking a UDF (<b>is_vip</b>) from SQL,
with  Figure 3 providing the implementation of the <b>is_vip</b> UDF, which 
returns whether a customer is a VIP. The <b>is_vip</b> UDF mixes declarative code
(the <b>SELECT</b> statement) and procedural code (<b>IF/ELSE</b> statements). Allowing
users to mix procedural and declarative code provides a more convenient and intuitive way
to express query logic than pure SQL. As a result, UDFs provide
[significant software engineering benefits](https://learn.microsoft.com/en-us/sql/relational-databases/user-defined-functions/user-defined-functions?view=sql-server-ver16)
 to database users, namely the ability to reuse code, express query logic more concisely, 
and decompose complex queries into modular functions.

# Row-By-Agonizing-Row (RBAR) Execution

Unfortunately, UDFs come with a performance cost. Unlike SQL, which is purely declarative, UDFs mix declarative and procedural programming paradigms.
A DBMS's query optimizer can effectively reason about SQL, but was never designed to optimize non-declarative UDF code.
As a consequence, DBMS's execute UDFs as opaque functions (much like built-in functions), evaluating them in a naive "row-by-row" fashion.
In the process, <b>SELECT</b> statements embedded inside the UDF are re-evaluated
for each row, dramatically slowing down query execution. Database practitioners have
termed this naive, inefficient, row-by-row execution of UDFs as [RBAR (Row-By-Agonizing-Row)](https://www.red-gate.com/simple-talk/databases/sql-server/t-sql-programming-sql-server/rbar-row-by-agonizing-row/).

For the query shown in Figure 2, the DBMS naively evaluates the UDF for each input row of the <b>customer</b> table. 
Each UDF call executes an embedded <b>SELECT</b> statement that accesses the <b>orders</b> table.
Without an available index on the <b>orders</b> table, the DBMS scans the entire table on each UDF invocation.
Hence, the query's runtime complexity is <b>Θ(|customer| × |orders|)</b>, which is extremely inefficient. With an index,
the DBMS can avoid rescanning the <b>orders</b> table, but each UDF still incurs significant overhead, resulting in
degraded query runtime.

# UDF Inlining: Intuition

<img src="intuition.png" alt="Figure 4: UDF Inlining Intuition." width="80%" />
<p style="text-align: left;">
<b>Figure 4, UDF Inlining Intuition:</b>
<em>
The key intuition behind UDF inlining is to translate UDFs from procedural functions into SQL subqueries,
a declarative representation that the DBMS can optimize effectively. In the above example, inlining replaces the <b>is_vip</b> UDF by an equivalent SQL subquery.
</em></p>

The DBMS employs RBAR execution of UDFs as they are written in a 
non-declarative paradigm that the query optimizer cannot effectively reason about. Such row-by-row
execution is reminiscent of how database systems logically evaluate SQL subqueries, 
whereby the DBMS re-evaluates a subquery for each row of the calling query. The key 
distinction, however, between UDFs and subqueries is that the database community has 
spent [decades optimizing subqueries](https://materialize.com/blog/decorrelation-subquery-optimization/).
Hence, if the DBMS could translate a UDF into an 
equivalent SQL subquery, the query is left entirely in SQL, which is amenable to 
effective query optimization. Translating UDFs to equivalent SQL subqueries is 
known as [<b>UDF inlining</b>](https://www.vldb.org/pvldb/vol11/p432-ramachandra.pdf), and enables the efficient execution of queries containing UDFs.

# Subquery Unnesting

![Figure 5: Subquery Unnesting.](subquery.png)
<p style="text-align: left;">
<b>Figure 5, Subquery Unnesting:</b>
<em>
An illustration of how DBMSs perform subquery unnesting. The SQL query is rewritten from
an inefficient query containing a subquery to an equivalent query containing joins that are significantly faster to execute.
</em></p>

UDF inlining avoids RBAR execution by translating UDFs into subqueries that the DBMS can <b>unnest</b>, replacing subqueries with equivalent join operators.

On the left-hand side of Figure 5 is a SQL query containing a subquery (shown in red).
The naive way of evaluating the query is by re-evaluating the subquery for each row of 
the <b>orders</b> table and rescanning the <b>customer</b> table. Evaluating the query in
this manner results in a runtime of <b>Θ(|customer| × |orders|)</b>, which is highly inefficient. The right-hand side of Figure 5 illustrates the rewritten query after the DBMS performs subquery unnesting, efficiently evaluating the query in <b>Θ(|customer| + |orders|)</b> time with hash joins.

# UDF Inlining: Further Details

<img src="inlining.png" alt="Figure 6: UDF Inlining." width="70%" />
<p style="text-align: left;">
<b>Figure 6, UDF Inlining:</b>
<em>
An illustration of the UDF inlining technique for our motivating example.
Inlining translates the <b>is_vip</b> UDF into an equivalent SQL subquery with <b>LATERAL</b> joins. 
The generated subquery is then "inlined" into the calling query.
After inlining, the query is represented entirely in SQL, which the DBMS can optimize 
effectively.
</em></p>

[UDF inlining](https://www.vldb.org/pvldb/vol11/p432-ramachandra.pdf) translates UDFs into equivalent SQL subqueries in three key steps. First,
inlining translates a UDF's statements to SQL tables. <b>IF/ELSE</b> blocks become 
<b>CASE WHEN</b> statements, assignments (i.e., <b>x = y</b>) become projections (i.e., <b>SELECT y AS x</b>).
Then, the DBMS chains together these statements with <b>LATERAL</b> joins. <b>LATERAL</b> joins are special joins
which allow the joining tables to reference each other's columns. After inserting <b>LATERAL</b> joins, the resulting
SQL expression is equivalent to the original UDF. The last step is to 
 "inline" the generated SQL expression into the calling query, eliminating the UDF call.
  After applying UDF inlining, queries are represented in pure SQL, automatically
improving the performance of queries with UDFs by [multiple orders of magnitude](https://www.vldb.org/pvldb/vol11/p432-ramachandra.pdf).

# The Problem with UDF Inlining

Unfortunately, UDF inlining is [ineffective](https://www.cidrdb.org/cidr2024/papers/p13-franz.pdf) for most real-world queries because it produces large,
 complex SQL queries that are hard to optimize. In particular, to achieve significant performance improvements with UDF inlining, 
the DBMS must unnest the generated subquery. Yet, UDF inlining produces complex subqueries containing <b>LATERAL</b> joins that [most DBMSs fail to unnest](https://www.cidrdb.org/cidr2024/papers/p13-franz.pdf).
 As a result, the DBMS evaluates the subquery naively for each row, akin to the RBAR execution strategy used before applying UDF inlining.


![Figure 7: Subquery Unnesting (ProcBench).](cant-unnest.png)
<p style="text-align: left;">
<b>Figure 7, Subquery Unnesting (ProcBench):</b>
<em>
A table indicating whether a given DBMS (SQL Server or DuckDB) successfully unnested a UDF-centric
query from the Microsoft SQL ProcBench. A green tick indicates that the unnesting succeeded. A grey cross
 indicates that the unnesting failed.
</em></p>

To understand how effectively DBMSs optimize queries with UDFs, we ran the [Microsoft 
SQL ProcBench](http://www.vldb.org/pvldb/vol14/p1378-ramachandra.pdf), a UDF-centric benchmark containing 15 queries 
modeled after real-world customer queries. We evaluated these queries on two DBMSs:
Microsoft SQL Server and DuckDB. A query executes efficiently only if the DBMS can 
unnest the subquery generated by UDF inlining otherwise the DBMS evaluates it RBAR. 
SQL Server unnests only 4 out of 15 of the queries after inlining. Alternatively stated,
SQL Server evaluates 11 out of 15 of the ProcBench queries RBAR, resulting in underwhelming 
performance. Hence, for most real-world UDF-centric queries, inlining is
ineffective on SQL Server. Although DuckDB supports
[arbitrary unnesting of subqueries](https://subs.emis.de/LNI/Proceedings/Proceedings241/383.pdf) and achieves
high performance on all 15 queries, only a [handful of DBMSs implement arbitrary unnesting](https://www.cidrdb.org/cidr2024/papers/p13-franz.pdf),
and integrating the optimization into existing systems is highly challenging. Hence,
for the majority of UDF-centric queries, inlining is
 [ineffective for the vast majority of DBMSs](https://www.cidrdb.org/cidr2024/papers/p13-franz.pdf) (shown in Figure 8).

# Our Solution: UDF Outlining

Fundamentally, we observe that inlining <b>entire UDFs</b> results in complex subqueries that are challenging for the DBMS
to unnest. Instead of inlining entire UDFs, a better approach is to analyze the UDF, deconstruct it into smaller pieces, and 
inline only the  pieces that help query optimization. To achieve this, we propose <b>UDF outlining</b>, an optimization technique 
that extracts UDF code fragments into separate functions that are intentionally not inlined, minimizing UDF code complexity. 
We implement UDF outlining in conjunction with four other complementary UDF-centric optimizations in <b>PRISM</b>, our optimizing compiler for UDFs (shown in Figure 9).    

<img src="prism.png" alt="Figure 8: PRISM." width="70%" />
<p style="text-align: left;">
<b>Figure 8, PRISM:</b>
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

To illustrate PRISM's optimizations, we illustrate the changes that occur when applying the three relevant optimizations to our motivating example.

# Region-Based UDF Outlining

The first and most critical optimization that PRISM performs is region-based UDF outlining. The goal of UDF outlining is to extract the largest blocks of unhelpful code 
for query optimization into separate functions that are opaque to the DBMS. PRISM achieves this by representing a UDF as [a hierarchy of program regions](https://dl.acm.org/doi/pdf/10.1145/178243.178258), where each region is eligible for outlining. PRISM identifies the largest regions of UDF code that do not contain any <b>SELECT</b> statements and extracts each
region into a separate outlined function. PRISM then compiles the outlined functions to machine code, preventing the inlining of the corresponding region. Lastly, PRISM replaces the
region in the original UDF with an opaque function call into the outlined function, simplifying the UDF substantially.

<img src="outlining.png" alt="Figure 9: Region-Based UDF Outlining." width="80%" />
<p style="text-align: left;">
<b>Figure 9, Region-Based UDF Outlining:</b>
<em>Instead of inlining the entire UDF, PRISM extracts the largest regions of non-<b>SELECT</b> code into separate outlined functions. In our example,
PRISM extracts the <b>IF/ELSE</b> block and <b>RETURN</b> statement into an outlined function <b>f(...)</b>, which is opaque to the query optimizer.
</em></p>

Figure 9 illustrates how PRISM applies region-based UDF outlining to our motivating example. First, PRISM identifies the region containing the <b>IF/ELSE</b> block and <b>RETURN</b> statement as the largest region not containing <b>SELECT</b> statements. Next, it extracts the region into a new outlined function <b>f(...)</b>, compiles it to machine code,
and replaces the original region with an opaque function call to the outlined function. Through UDF outlining, PRISM significantly simplifies the UDF,
 enabling more effective query optimization.

# Instruction Elimination

PRISM then applies instruction elimination, eliminating as many redundant instructions in the UDF as possible. PRISM achieves this by replacing a variable's uses
with its definition, making the variable definition redundant. PRISM then deletes the definition. 
PRISM eliminates redundant instructions through instruction elimination, minimizing the number of <b>LATERAL</b> joins generated from inlining.

<img src="instruction.png" alt="Figure 10: Instruction Elimination." width="80%" />
<p style="text-align: left;">
<b>Figure 10, Instruction Elimination:</b> After UDF outlining, PRISM applies instruction elimination to remove as many UDF instructions as possible, reducing 
the number of <b>LATERAL</b> joins from inlining. Instruction elimination replaces the uses of a variable with its definitions. In our example,
PRISM eliminates the definition of <b>total</b>, directly forwarding its definition to the use by <b>f(...)</b>.
<em>
</em></p>

Figure 10 showcases PRISM's application of instruction elimination to our motivating example. PRISM identifies <b>total</b> as a program variable
and replaces its use in <b>f(...)</b> with its definition. Since <b>total</b> no longer has any uses, PRISM eliminates its defining instruction, collapsing the
UDF to a single <b>RETURN</b> statement.

# Subquery Elision

Lastly, PRISM runs subquery elision to eliminate redundant subqueries from the resulting query. Inlining translates UDFs into subqueries, which complicates
query optimization. However, PRISM elides the subquery when a UDF consists of a single <b>RETURN</b> statement (as is the case for our motivating example, shown in Figure 11).
Instead, it directly substitutes the original UDF call with the return value. PRISM simplifies the UDF through its optimizations,
oftentimes leaving the resulting query free of <b>LATERAL</b> joins, resulting in more effective query optimization and faster query plans.

<img src="elision.png" alt="Figure 11: Subquery Elision." width="60%" />
<p style="text-align: left;">
<b>Figure 11, Subquery Elision:</b>
<em>In our example, PRISM reduces the UDF to a single <b>RETURN</b> statement after instruction elimination. When a UDF consists of a single <b>RETURN</b> statement,
 PRISM performs subquery elision and injects the return value into the calling query rather than substituting it as a SQL subquery.
</em></p>


# Experimental Setup

We performed our evaluation on a machine with a dual-socket 20-core Intel Xeon Gold 5218R CPU (20 cores per CPU, 2× HT), 192 GB DDR4 RAM, and a 960 GB NVMe SSD.
We use the default index configuration for all workloads and build additional column-store indexes on every table on SQL Server. For each DBMS, we tune their configuration
 knobs to improve performance, pre-warm the buffer pool, and refresh statistics. We perform two warmup runs of each query and then five hot runs (with minimal observed variance), 
 reporting the average execution time of the five runs.

<b>SQL ProcBench</b>: Microsoft released the [SQL ProcBench](http://www.vldb.org/pvldb/vol14/p1378-ramachandra.pdf) in 2021 as the first UDF-centric benchmark modeled after real-world UDFs on Azure SQL Server. ProcBench is based on the TPC-DS benchmark and contains 24 queries that invoke scalar UDFs. We use a scale factor of 10 (a database size of ≈10 GB). We run 15 of the 24 queries, ignoring queries that use table-valued functions (TVFs) or UDFs invoked from stored procedures.

# Experiments: Unnesting

![Figure 12: Subquery Unnesting (ProcBench).](unnest.png)
<p style="text-align: left;">
<b>Figure 12, Subquery Unnesting (ProcBench):</b>
<em>
 A table indicating whether a given DBMS (SQL Server or DuckDB) successfully unnested a UDF-centric query
from the Microsoft SQL ProcBench with a given technique (inlining or PRISM). A green tick indicates that the unnesting succeeded.
 A grey cross indicates that the unnesting failed. Figure 12 and Figure 7 share the same values for the queries unnested with inlining.
</em></p>

The principle issue with UDF inlining is that it produces complex subqueries with <b>LATERAL</b> joins
that most DBMSs cannot unnest, resulting in inefficient RBAR execution. By comparison, PRISM only exposes
the UDF pieces that improve query optimization, resulting in significantly simpler and faster queries.
As shown in Figure 12, SQL Server can unnest only 4 out of 15 of the ProcBench queries after applying UDF inlining.
Yet with PRISM, SQL Server can unnest 12 of the 15 queries, leading to efficient query execution with joins
rather than inefficient RBAR execution. As expected, DuckDB can unnest all 15 queries with both techniques,
as it supports arbitrary unnesting of subqueries. In summary, PRISM significantly improves
subquery unnesting compared to naively inlining the entire UDF.

# Experiments: Overall Speedup

<img src="speedup.png" alt="Figure 13: Overall Speedup (ProcBench)." width="70%" />
<p style="text-align: left;">
<b>Figure 13, Aritmethic Mean Speedup (ProcBench):</b>
<em>
A table indicating the overall speedup on the Microsoft SQL ProcBench when running queries with PRISM over inlining the entire UDF.
We calculate speedup by dividing the runtime of running a given query without PRISM (i.e., inlining the entire UDF) by the runtime with PRISM.
We report the arithmetic mean speedup (excluding outliers) and the maximum speedup (including outliers). We observe that PRISM provides significant performance improvements over existing UDF optimization techniques.
</em></p>

Figure 13 details the arithmetic mean (average) and maximum speedup of the ProcBench queries when running PRISM. We observe that, on average, PRISM attains a speedup of 298.7× due to 8 of the 15 ProcBench queries now evaluating efficiently with joins after successful unnesting rather than RBAR. The maximum speedup for SQL Server is 2997.9×, again due to more effective unnesting,
for a query that spends the entirety of its execution time in the UDF call. DuckDB can unnest arbitrary queries. Therefore, PRISM offers a more modest arithmetic mean speedup of 1.29× due to 
eliminating <b>LATERAL</b> joins from the query plan. Lastly, PRISM delivers a maximum speedup of 2270.2× on DuckDB, as the query after UDF inlining is so complex, that even after unnesting, the DBMS picks an inefficient query plan with a large cross-product.  In contrast, the generated query is substantially simpler with PRISM,  leading to an efficient plan 
evaluated with hash joins. PRISM significantly improves SQL Server and DuckDB compared to inlining entire UDFs by generating simpler queries that are easier to optimize.

# Conclusion

The database community developed UDF inlining to translate entire  UDFs to SQL for more effective query optimization. We observe that inlining entire UDFs leads to complex, obfuscated queries that are challenging for DBMSs to optimize effectively. Instead, we propose UDF outlining, a new technique that extracts regions of code irrelevant for query optimization into opaque functions intentionally hidden from the DBMS. In addition to UDF outlining, our optimizing compiler (PRISM) supports four other complementary UDF-centric optimizations.
By generating simpler queries, we observe that on the Microsoft SQL ProcBench, PRISM provides dramatic performance improvements over inlining entire UDFs.

Our paper has been [accepted for publication in VLDB 2025](https://www.vldb.org/pvldb/vol18/p1-arch.pdf).