# DataAbstraction
# From Horn clause with array invariants to Horn clauses without array invariants

Julien Braine
Licence: GPL

Input: a smt2 file
Output: a smt2 file where arrays in predicates are abstracted using "1 cell abstraction"

Usage : ./dataabs [options] file

Example : ./dataabs demo.smt2

Use your favorite SMT solver to solve the resulting smt2 file
