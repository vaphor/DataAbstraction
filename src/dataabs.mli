open Expr
open Horn

module Insts_set : (Set.S with type elt =expr*expr)
type insts_set = Insts_set.t

type abstraction =
{
  name : string;
  concrete_type : expr;
  abstract_type : expr;
  fsigmaq : expr (*quants*) -> expr -> expr -> expr;
  fsigma : expr -> expr -> expr;
  insts : expr -> expr -> insts_set;
}

val abs_annotation : (abstraction * expr * expr) Hmap.key

(* Abstracts a predicate with an abstraction (yielding a new predicate) in an expression.
   Abstracted elements are stored in the annotation abs which is used for eliminate*)
val abstract : abstraction -> expr (*predicatetoabs*) -> expr (*newpredicate*)-> expr (*expression*) -> expr

(*eliminates the introduced quantifiers*)
val eliminate : expr -> expr

(*applies both*)
val dataabs : abstraction -> expr (*predicatetoabs*) -> expr (*newpredicate*)-> expr (*expression*) -> expr

(* function that to a predicate associates the new predicate name and the abstraction that should be applied to it*)
val abstract_horn : (string -> expr (*predtype*) -> (string * abstraction)) -> horn -> horn
val eliminate_horn : horn -> horn
val dataabs_horn : (string -> expr -> (string * abstraction)) -> horn -> horn
