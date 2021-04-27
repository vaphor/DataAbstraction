open Horn 
open Expr

val parse_expr : string (*expression*)-> expr
val import_expr : string (*filename*) -> expr
val print_expr_smt2 : expr -> string
val export_expr_smt2 : expr -> string -> unit

val parse_horn : string (*expression*)-> horn
val import_horn : string (*filename*) -> horn
val print_horn_smt2 : horn -> string
val export_horn_smt2 : horn -> string -> unit


