open Dataabs
open Expr

val mk_cellabs : expr (*index type*) -> expr (*value type*) -> abstraction
val mk_currified_cellabs : expr (*index type*) -> expr (*value type*) -> abstraction
