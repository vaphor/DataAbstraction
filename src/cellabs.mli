open Dataabs
open Expr

val mk_cellabs : expr (*index type*) -> expr (*value type*) -> abstraction
val mk_combined_abs : expr -> abstraction
val mk_currified_cellabs : expr (*index type*) -> expr (*value type*) -> abstraction
val fsort : expr list -> expr
val comp : expr -> expr -> expr
