open Expr
open Io
open Dataabs
open Combinators
open Cellabs


type full_abs=string (*pname*) -> expr (*ptype*) -> (string (*abs panme*) * abstraction (*abstraction*))

val all_arrays_cell : int -> full_abs

val smash_all : full_abs
