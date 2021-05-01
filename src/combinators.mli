

open Expr
open Dataabs


val mk_id : expr (*type*) -> abstraction
val tuple_dot: abstraction list -> abstraction
val compose : abstraction -> abstraction -> abstraction
val duplicate : abstraction -> int -> abstraction
