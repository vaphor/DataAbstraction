

open Expr
open Io
open Config
open Dataabs
open Combinators
open Cellabs
open Horn
open Fullabstractions

let get_full_abs_from_name str =
  match str with
  | celln when (String.sub str 0 4) = "Cell" -> all_arrays_cell (int_of_string (String.sub str 4 ((String.length str) - 4))) 
  | curccelln when (String.sub str 0 7) = "CurCell" -> all_arrays_curr_cell (int_of_string (String.sub str 7 ((String.length str) - 7))) 
  | samecelln when (String.sub str 0 8) = "SameCell" -> array_cell_same_index2 (int_of_string (String.sub str 8 ((String.length str) - 8))) 
  | samecelln when (String.sub str 0 11) = "revSameCell" -> array_cell_same_index2rev (int_of_string (String.sub str 11 ((String.length str) - 11))) 
  | "Smashing" -> smash_all
  | _ -> failwith (Printf.sprintf "Unknown abstraction %s" str)


  

  

let __ =
  Printexc.record_backtrace(true);
  try
    let cf = read_args() in
(*     Printexc.record_backtrace(false); *)
    if cf.debug then Printf.printf "File is %s\n" cf.f_name;
    let myabs = get_full_abs_from_name cf.abstraction in
    let h = import_horn cf.f_name in
    let abstracted = if cf.abstract_only then abstract_horn myabs h else dataabs_horn myabs h in
    let simplified = if cf.simplify then Horn.simplify ~acker:cf.acker abstracted else abstracted in
    export_horn_smt2 simplified cf.outputsmt_name
   with
    (*Whenever an exception is thrown, print expression and backtrace (empty if debug = false), and exit with -1 status*)
    | e -> Printf.printf "\n\nException : %s %s\n\n" (Printexc.to_string e) (Printexc.get_backtrace ()); exit (-1)
