__Author__ : Julien Braine

__Licence__ : GPL

# About

The tool implements a technique to transform Horn clauses which require array invariants so solve them into
Horn clauses that do not need array invariants by using an abstraction scheme. The technique is described in the paper 
*Data Abstraction: A General Framework to Handle Program Verification of Data Structures* presented to SAS2021. 
It is currently set to use the full algorithm using Cell^n abstraction presented in Algorithm 6, page 5.

The tool is an element of a static program (or other) verification process which is done in three steps:
1. Transform the verification problem into Horn clauses, perhaps using [MiniJavaConverter](https://github.com/vaphor/hornconverter) or [SeaHorn](https://github.com/seahorn/seahorn)
2. This tool which simplifies the Horn clauses using abstraction.
3. A Horn solver such as [Z3](https://github.com/Z3Prover/z3)

The full toolchain using [MiniJavaConverter](https://github.com/vaphor/hornconverter) and [Z3](https://github.com/Z3Prover/z3), docker and benchmarks are available at [array-benchmarks](https://github.com/vaphor/array-benchmarks).


# Installing the tool

## Dependencies

The tool is written in Ocaml and we use
- ocamlbuild
- the Hmap package

## Install

Running `make` should build the tool and create an executable named *dataabs*.

## Test

Run `make demo` to check that the tool run correctly on *demo.smt2* and, if you have [Z3](https://github.com/Z3Prover/z3) installed, use `make test` to check the result
of the demo. Full benchmarks are available at [array-benchmarks](https://github.com/vaphor/array-benchmarks).

# Running the tool

## Default run 

Run `./dataabs in.smt2` where *in.smt2* represents the smt2 file containing the clauses to abstract.
The output is written on *stdout* and is in smt2 format and represents the abstracted clauses.
The abstraction used is *Cell^1* on all arrays of all predicates.

## Options

The tool's options can be displayed with `./dataabs -h`. The most relevant options are:
1. `-o outfile.smt2` changes output to outfile.smt2 instead of *stdout*
2. `-nbcells n` changes the abstraction used to *Cell^n* instead of Cell^1
3. `-acker` applies Ackermannisation to further remove arrays.

# Source code

## Source code organization
The source code is available in the *src* folder. The files in them can be divided into three categories:
1. Utility files:  *horn_lexer.mll localizing.ml/mli horn_parser.mly config.ml io.ml/mli*
2. Base classes : *expr.ml/mli horn.ml/mli*. In this tool, we do not limit the theory on which expressions are based. 
   Therefore, non quantified expressions are simply Cons(str, args, _) where str denotes the constructor (+, and, or, ...).
   We use *Higher-order abstract syntax* to handle binders (quantifiers): a binder is an ocaml function that to a name associates the expression.
   *expr.ml* contains simplifications algorithms.
   Horn problems are modeled by a set of expressions (clauses) and a list of predicates.
3. Files in relation to our DataAbstraction technique:
    1. *dataabs.ml/mli* defines *abstract* which is Algorithm 1, page 7 of the SAS2021 paper, *eliminate*  which is Algorithm 2, page 9 of the SAS2021 paper
        and their lifting from expressions to Horn problems and their combination *dataabs/dataabs_horn*.
    2. *combinators.ml/mli* defines combinators for data abstractions (Definition 9, page 7 and Algorithms 3 and 4, page 11). Among them:
        - *mk_id* : the identity abstraction
        - *tuple_dot* : generalizes the dot combinator for pairs to tuples.
        - *compose* : the composition combinator
        - *duplicate* : which duplicates the abstraction used. For example, `Cell^n = duplicate Cell^1 n`. This is not described in the paper.
    3. *cellabs.ml/mli* defines Cell^1. We do not need to define Cell^n as Cell^n can be constructed from Cell^1 and *duplicate*.
       It contains Algorithms 5 and 6, page 14 of the paper.
4. The full algorithm written in *main.ml*. Note that Algorithm 7, page 15 is mostly in *main.ml* except that the combination of *abstract* and *eliminate* is already done in *dataabs.ml*.
   The abstraction that is used, that is, abstracting all arrays of all predicates by Cell^n is described by the function *myabs*.

## Creating and using a new abstraction

New abstractions can be created by defining a new abstraction from scratch and/or by combining existing abstractions differently.
To illustrate both, we show how to use *array smashing* (Example 9, page 13 of the paper) on all arrays of all predicates.
We use the following steps:
1. Define a new abstraction *forget_first* and combine it with *Cell^1* to create the *array_smashing* abstraction.
2. Modify *myabs* from *main.ml* so that *array_smashing* is used on all array variables of all predicates.

### Defining the array smashing abstraction

```ocaml
(*Abstracts an expression of type pair(t1, t2) into t2.
  Equivalent to forget.id of the paper.
  sigma_{forget_first}(e1,e2) = \{e2\} *)
let forget_first t1 t2 =                                                                                                                                                                                              
  {                                                                                                                                                                                                        
    name = Printf.sprintf "forgetfst";                                                                                                                                                                            
    concrete_type = mk_tuple [t1;t2];                                                                                                                                                                                     
    abstract_type = t2;  
    fsigma = (fun abstract conc -> Cons("=", [abstract; (esnd conc)], Hmap.empty));   
    (*fsigmaq is not defined automatically from fsigma, this may happend in the near future*)
    fsigmaq = (fun q abstract conc -> Cons("=", [abstract; (esnd conc)], Hmap.empty));  
    (*The instantiation is finite, we thus use [e2] as instantiation set and it is strongly complete*)
    insts = fun a ctx -> Insts_set.singleton (esnd a, mk_unit);                                                                                                                                                 
  }  
  
(*indtype (recpectively valtype) is the index (respectively value) type of the array to abstract*)
let array_smashing indtype valtype =  compose (forget_first indtype valtype) (mk_cellabs indtype valtype)
```
## Using it on all arrays of all predicates

We only need to change the *myabs* function from *main.ml*
```ocaml
let myabs n pname ptype =
   let rec create_abs ptype =
    match ptype with
     | Cons("Tuple", l, a) -> (*Tuples are abstracted by the tuple abstraction*)
         tuple_dot (List.map create_abs l)
     | Cons("Array", [indtype;valtype], a) -> (*Arrays are abstracted by array smashing*)
         array_smashing indtype valtype
     | _ -> mk_id ptype (*Other types are abstracted by the identity*)
   in
   (pname^"_abs", create_abs ptype) (*We return the name for the abstracted predicate and the abstraction*)
```

Note: one may not one to abstract uniformly all predicates and all arrays. 
This can be avoided by doing different things depending on *pname* or the position of the array in the tuple
(do not do `(List.map create_abs l)` which applies *create_abs* on all parameters uniformely).
