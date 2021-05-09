

open Expr
open Dataabs


val mk_id : expr (*type*) -> abstraction
val tuple_dot: abstraction list -> abstraction
val compose : abstraction -> abstraction -> abstraction
val duplicate : abstraction -> int -> abstraction

(*reorganizes tuples. This can do swap, duplication, forget, ...
Example reorganize_tuples ((int, string), (bool, (string, int)) "(0.0, (1.0, 0.0), 1.1.0)"
transforms P ((a,b), (c, (d,e))) into P_abs(a, (c, a), d) *)
val reorganize_tuples : expr(*initial type*) -> expr (*new tuple tree*) -> abstraction

val restrict : expr(*initial type*) -> (expr -> expr(*of bool type*)) (*condition*) -> abstraction
val union : expr(*initial type*) -> abstraction
