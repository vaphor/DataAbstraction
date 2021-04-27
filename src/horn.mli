open Expr

type command =
| Comment of string
| Clause of expr

type horn = (command list) * ((string * expr) list) (*predicate declaration*)

val transform_clauses : (expr -> expr) -> horn -> horn

val simplify : ?acker:bool -> horn -> horn
