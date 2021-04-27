

open Expr
open Io
open Config
open Dataabs
open Combinators
open Cellabs
open Horn

let myabs n pname ptype =
   let rec create_abs ptype =
    match ptype with
     | Cons("Tuple", l, a) -> 
         tuple_dot (List.map create_abs l)
     | Cons("Array", [t1;(Cons("Array", [ind2; v2],_) as t2)], a) -> 
         duplicate (compose (dot (mk_id t1) (mk_cellabs ind2 v2)) (mk_cellabs t1 t2)) n
     | Cons("Array", [t1;t2], a) -> 
         duplicate (mk_cellabs t1 t2) n
     | _ -> mk_id ptype 
   in
   (pname^"_abs", create_abs ptype)
   

let __ =
  Printexc.record_backtrace(true);
  try
    let cf = read_args() in
    Printexc.record_backtrace(false);
    if cf.debug then Printf.printf "File is %s\n" cf.f_name;
    let h = import_horn cf.f_name in
    let abstracted = if cf.abstract_only then abstract_horn (myabs cf.distinct_i) h else dataabs_horn (myabs cf.distinct_i) h in
    let simplified = if cf.simplify then Horn.simplify ~acker:cf.acker abstracted else abstracted in
    export_horn_smt2 simplified cf.outputsmt_name
   with
    (*Whenever an exception is thrown, print expression and backtrace (empty if debug = false), and exit with -1 status*)
    | e -> Printf.printf "\n\nException : %s %s\n\n" (Printexc.to_string e) (Printexc.get_backtrace ()); exit (-1)
