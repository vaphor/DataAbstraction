open Expr
open Horn

let debug_parse parsefct lexbuf = 
  let r = 
    try parsefct Horn_lexer.token lexbuf
    with exn ->
      begin
        let curr = lexbuf.Lexing.lex_curr_p in
        let line = curr.Lexing.pos_lnum in
        let cnum = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
        let tok = Lexing.lexeme lexbuf in
        let tail = Horn_lexer.ruleTail "" lexbuf in
        failwith (Printf.sprintf "Problem when parsing (probably due to characters just before) %s %i %i" (tok^tail) cnum line ) 
      end in
   r
   
let parse_expr_buf lexbuf =
  debug_parse Horn_parser.expr lexbuf
  
let parse_horn_buf lexbuf =
  let h = debug_parse Horn_parser.horn lexbuf in
  let transform c =
     List.fold_left (
       fun newc (pname, ptype) -> 
         replace_all_opt (fun e -> 
                            match e with
                            | Cons(p, args, a) when p = pname -> Some(Cons("apply", [Cons(p, [], Hmap.empty); mk_tuple args], a))
                            | _ -> None) 
                          newc
         )
         c (snd h) in
   Horn.transform_clauses transform h
   
   

   
let parse_expr str=  
  let lexbuf = Lexing.from_string str in
  parse_expr_buf lexbuf
  
let import_expr filename=  
  let f_desc = try open_in filename
  with 
    | Sys_error(e) -> failwith ("Impossible to open file. Filename read is \""^filename^"\"") in
  let lexbuf = Lexing.from_channel f_desc in
  parse_expr_buf lexbuf
  
  
let parse_horn str=  
  let lexbuf = Lexing.from_string str in
  parse_horn_buf lexbuf
  
let import_horn filename=  
  let f_desc = try open_in filename
  with 
    | Sys_error(e) -> failwith ("Impossible to open file. Filename read is \""^filename^"\"") in
  let lexbuf = Lexing.from_channel f_desc in
  parse_horn_buf lexbuf
  
    
let rec print_expr_smt2 expr =
  let e = binders_as_cons expr in
  let rec extract_all_foralls e =
    match e with
    | Cons("forall", [vn;vt;f], _) -> let (oforalls, rest) = extract_all_foralls f in
                                          ((vn, vt)::oforalls, rest)
    | _ -> ([], e) in
  let (decl, rest) = extract_all_foralls e in  
    
  let print_rest =
    match rest with
    | Cons(str, [], _) -> Printf.sprintf "%s" str
    | Cons(str, l, _) -> Printf.sprintf "(%s %s)" str (String.concat " " (List.map print_expr_smt2 l))
    | _ -> failwith "no binders expected here"
  in
  
    match decl with
    | [] -> print_rest
    | l -> let tmp = List.fold_left (fun str (vn, vt) -> Printf.sprintf "%s (%s %s)" str (print_expr_smt2 vn) (print_expr_smt2 vt)) "" l in
           Printf.sprintf "(forall (%s) %s)" tmp print_rest
           
let export_expr_smt2 e file=
  let str = print_expr_smt2 e in
  if file = "stdout" then 
      Printf.printf "%s" str
    else
      let outfile = open_out file in
      Printf.fprintf outfile "%s" str           

      
      
let print_horn_smt2 h =
 (*Flattening apply P tuple(...) *)
 let rec nt vt =
   match Expr.simplify vt with 
      | Cons("Tuple", l, _) -> List.flatten (List.map nt l)
      | x -> [x] in
 let rec f vt arg  =
      match vt with 
      | Cons("Tuple", l, a) -> List.flatten (List.mapi (fun i x -> (f x (extract arg i))) l)
      | _ -> [arg] in
  let declp = (String.concat "\n" (List.map (fun (pn, pt) -> Printf.sprintf "(declare-rel %s (%s))" pn (String.concat " " (List.map print_expr_smt2 (nt pt)))) (snd h)))^"\n" in
  
      
  
  let rec flattenP vn vt e =
        replace_all_opt (fun e -> match e with 
                          | Cons("apply", [a;b], m) when equiv a (mk_const vn) -> Some(simplify_tuples (Cons(vn, f vt b, m)))
                          | _ -> None) e in
    
    
  let (newc, _) = transform_clauses (fun c ->
    List.fold_left (fun newe (vn, vt) -> flattenP vn vt newe) c (snd h)) h in
        
  let c = String.concat "\n" (List.map (fun c -> 
    match c with
    | Comment(str) -> ";"^str
    | Clause(e) -> Printf.sprintf "(assert %s)" (print_expr_smt2 e)) (newc)) in
  "\n(set-logic HORN)\n"^declp^c^"\n(check-sat)\n"
  
  
let export_horn_smt2 h file=
  let str = print_horn_smt2 h in
  if file = "stdout" then 
      Printf.printf "%s" str
    else
      let outfile = open_out file in
      Printf.fprintf outfile "%s" str
      
  
