(*This file is part of Vaphor

    Vaphor is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Vaphor is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with Vaphor.  If not, see <https://www.gnu.org/licenses/>. *)


open Format

(****** Command line + Software configuration *****)
type config_t = {
  f_name:string;
  outputsmt_name:string;
  distinct_i:int;
  debug:bool;
  version:string;
  acker:bool;
  abstract_only:bool;
  simplify:bool;
}
exception Version
exception Usage of string
exception NotFound of string
			

let set_outputsmt config (s:string) = config := {!config with outputsmt_name=s}
let set_debug config () = config := {!config with debug=true}
let set_acker config () = config := {!config with acker=true}
let set_abs_only config () = config := {!config with abstract_only=true}
let set_no_simplify config () = config := {!config with simplify=false}

let set_fname config (s:string) =  
  if Sys.file_exists s
  then config := {!config with f_name=s}
  else raise (NotFound s) 

let set_di config nb =
  if (nb < 1)
  then raise (Usage "nb distinguished should be >= 1")
  else config := {!config with distinct_i=nb}
					   
let make_default_config () = {
  f_name="";
  outputsmt_name="stdout";
  distinct_i = 1;
  debug=false;
  version="NA";
  acker=false;
  abstract_only=false;
  simplify=true;
}
			       
let string_config cf =
  Printf.sprintf "inputfile=%s,di=%d,acker=%b\n" cf.f_name cf.distinct_i cf.acker
			       
let read_args () =
  let cf = ref (make_default_config()) in
  let speclist = 
    [
      ("-absonly",Arg.Unit (set_abs_only cf) ,": only abstract");
      ("-no_simplify",Arg.Unit (set_no_simplify cf) ,": do not simplify the result. This exposes internal theories.");
      ("-acker",Arg.Unit (set_acker cf) ,": ackermanise arrays when possible");
      ("-debug", Arg.Unit (set_debug cf) ,": all debug info");
      ("-nbcells", Arg.Int (set_di cf) ,": Number of cells used (n of Cell n abstraction)");
      ("-o", Arg.String (set_outputsmt cf) ,": outputfile, default is res.smt2");
    ] in
  let usage_msg = "Usage : ./vaphor [options] file.smt2" in
  try (Arg.parse speclist (set_fname cf) usage_msg; 
       if !cf.f_name = "" then begin Arg.usage speclist usage_msg ; raise (Usage usage_msg) end; 
       !cf 
  )
  with
  | Version -> exit(1)
  | Usage(_) -> exit(1)
