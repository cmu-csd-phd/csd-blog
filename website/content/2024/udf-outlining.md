+++
title = "The Key to Effective UDF Optimization: Before Inlining, First Perform Outlining"
date = 2024-08-10

[taxonomies]
areas = ["Systems"]
tags = ["database systems", "compiler optimization", "query optimization", "query languages"]

[extra]
author = {name = "Sam Arch", url = "www.samarch.xyz" }
committee = [
    {name = "Harry Q. Bovik", url = "http://www.cs.cmu.edu/~bovik/"},
    {name = "Committee Member 2's Full Name", url = "Committee Member 2's page"},
    {name = "Committee Member 3's Full Name", url = "Committee Member 3's page"}
]
+++

# Background

SQL is the defacto query language for interacting with database systems. Since SQL is a declarative programming language, users express the intended result of their query rather than the concrete procedural steps to produce the query result. Database systems execute SQL efficiently by using a component called the query optimizer. The optimizer's task is to search the space of equivalent query plans (specific procedural strategies to retrieve the result of a query) for a given SQL query and select the plan with the lowest estimated cost. After decades of research on query optimization, database systems have become remarkably good at executing SQL queries efficiently.

However, a large number of SQL queries make calls to User-Defined Functions (UDFs) which are procedural functions written in non-SQL programming languages such as Python or PL/SQL. Since UDFs are procedural (non-declarative) functions, they are opaque and the query optimizer cannot reason about them, leading to slow, inefficient query plans.

# RBAR with is_vip

# UDF Inlining

# UDF Outlining

# Experiments

# Conclusion