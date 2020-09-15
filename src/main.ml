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

(*
In this file, we give the main function of the program.
The goal of the program is to convert a horn problem in smt2 format 
into a horn problem in smt2 format with given types are abstracted.

To define a new abstraction, one needs to create an abstraction type (as defined in types.ml).

Once an abstraction is given, the program follows the following steps.

1) It parses the input file without understanding it : it only retrieves the well parenthesized expression
   This is done in horn_lexer.mll and horn_parser.mly.

2) We interpret the well parenthesized expressions : expressions starting with declare-fun and assert.
   This is done in interpret.ml

3) We apply the type abstraction and we recognize the abstract operation (without doing anything to them yet).
   This is done in transform.ml

4) We normalize the expression, so that we only need to abstract expressions of the form new_var = abstractop(...)
   This is done in normalization.ml

5) We finally abstract the operations.
   this is done in abstraction.ml

6) We simplify the expressions (get rid of tuples, ...)
   This is done in simplification.ml
*)




open Format
open Printexc
open Filename
open Config
open Expressions
[@@@warning "-8"]
let parse config =
  (*Checking Existence of input file*)
  if String.compare config.f_name "" = 0 then failwith ("No input file. Filename read is \""^config.f_name^"\"");
  Localizing.current_file_name := config.f_name;

  (*Opening file*)
  let f_desc = try open_in config.f_name 
  with 
    | Sys_error(e) -> failwith ("Impossible to open file. Filename read is \""^config.f_name^"\"") in

  (* Lexing *)
  let lexbuf = Lexing.from_channel f_desc in
  let horn_problem = 
    (*Parsing*)
    try Horn_parser.horn Horn_lexer.token lexbuf
    (*Retrieving where the error is*)
    with exn ->
      begin
        let curr = lexbuf.Lexing.lex_curr_p in
        let line = curr.Lexing.pos_lnum in
        let cnum = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
        let tok = Lexing.lexeme lexbuf in
        let tail = Horn_lexer.ruleTail "" lexbuf in
        failwith (Printf.sprintf "Problem when parsing (probably due to characters just before) %s %i %i" (tok^tail) cnum line )  (*raise (Error (exn,(line,cnum,tok)))*)
      end in
   horn_problem

  
let get_preds f = 
  let open Tree in
  Tree.fold2 (fun _ -> []) (fun l t -> match t with 
                             | Node([Leaf("exists", _); Node([p], _); f], _) -> p::(List.flatten l)
                             | _ -> List.flatten l) f
  
let print_tree t =
  Tree.fold (fun (str,_) -> str) 
        (fun strl _ -> match strl with
           | ["SEQ";a;b] -> Printf.sprintf "%s\n%s" a b
           | _ -> Printf.sprintf "(%s)" (String.concat " " strl)
        ) t
  
let rec as_formula t =
  let open Tree in
  let inone=None in
  Tree.rewrite_rec (fun t ->
  match t with
  | Node([Leaf("SEQ", _); Node([Leaf("declare-fun", i1); f; Node(argstypes, i2); ret], i3); ninst], i4) ->
    Some(Node([Leaf("exists", i1); 
        Node([
          Node([f; 
            Node(
            [
              Leaf("->", inone);
              Node(Leaf("tuple", inone)::argstypes, i2);
              ret
            ], inone)], i3)], inone); ninst], i4))
  | Node([Leaf("SEQ", i0); Node([Leaf("declare-rel", i1); f; args], i3); ninst], i4) -> 
      Some(Node([Leaf("SEQ", i0); Node([Leaf("declare-fun", i1); f; args; Leaf("Bool", inone)], i3); ninst], i4))
      
  | Node([Leaf("exists", _); vars; Node([Leaf("assert", _); e], _)], _) -> 
      Some(Node([Leaf("assert", inone); Node([Leaf("exists", inone); vars; e], inone)], inone))
  | Node([Leaf("SEQ", _); Node([Leaf("assert", _); e1], _); Node([Leaf("assert", _); e2], _)], _) -> 
    Some(Node([Leaf("assert", inone); Node([Leaf("and", inone);  e1;e2], inone)], inone))
  
  |  Node([Leaf("SEQ", _); f; Leaf("Skip", _)], _) -> Some(f)
  |  Node([Leaf("SEQ", _); f; Node([Leaf("check-sat", _)], _)], _) -> Some(f)
  |  Node([Leaf("SEQ", _); Node([Leaf("set-logic", _); h], _);f], _) -> Some(f)
  (*| Node(Leaf("SEQ", _)::Node(Leaf("declare-rel", i1)::l, _)::_, _) -> 
      Printf.printf "yes !\n"; t
  | Node(Leaf("SEQ", _)::Node(Leaf(_,_), _)::e::[], _) -> 
      Printf.printf "no !\n"; t*)
  | _ -> None) t
  
let rec from_formula f =
  let open Tree in
  let inone=None in
  Tree.rewrite_rec (fun t ->
(*Printf.printf "doing....\n";*)
  match t with
  | Node([Leaf("assert", _); Node([Leaf("exists", _); Node(preds, _); f], _)], _) ->
    begin
    match preds with
    | [Node([name; Node([Leaf("->", _); Node(Leaf("tuple", _)::argst, _); ret], _)], _)] -> 
        Some(Node([Leaf("SEQ", inone);
                Node([Leaf("declare-fun", inone); name; Node(argst, inone);ret], inone);
                Node([Leaf("assert", inone); f], inone);
             ], inone))
    | _ -> failwith (Printf.sprintf "not done yet : %i" (List.length preds))
    end
  | Node([Leaf("assert", _);Node([Leaf("and", _); f1;f2], _)],_) ->
        Some(Node(
          [
            Leaf("SEQ", inone);
            Node([Leaf("assert", inone); f1], inone); 
            Node([Leaf("assert", inone); f2], inone); 
        
          ], inone))
  | _-> None) f
    
type 'a abstraction =
{
  predicate : ('a, (string * 'a)) Tree.tree;
  new_type : ('a, (string * 'a)) Tree.tree;
  suggested_npred : ('a, (string * 'a)) Tree.tree;
  fsigma : ('a, (string * 'a)) Tree.tree -> ('a, (string * 'a)) Tree.tree list -> ('a, (string * 'a)) Tree.tree;
  (*instantiation : ('a, (string * 'a)) Tree.tree (*the used quantifier*) -> ('a, (string * 'a)) Tree.tree (*the clause*) -> ('a, (string * 'a)) Tree.tree list 
  (*the instantiation_set*)*)
}

(*f is a function that to a type associates an option of (new type and an fsigma and an instantiation : the concrete expression that is gonna be abstracted -> the abstracted clause -> instantiation list). preds is a list of expressions of the predicates to abstract*)
let mk_abstractions f preds =
  let open Tree in
  List.fold_left (fun abss p -> 
    let Node([Leaf(pname, inone); Node([Leaf("->", _); Node(Leaf("tuple", _)::argst, _); Leaf("Bool", _)], _)], _) =  p in
    let (suggested, new_types, fsigma, _ ) = 
     List.fold_left 
     (fun (pstr, types, fsigma, pos) t -> match f t with
      | None -> let put_equality vabs l = 
                   Node([
                       Leaf("and", inone); 
                       Node([Leaf("=", inone);Node([Leaf("tuple_get", inone);Leaf(Printf.sprintf "%i" pos, inone); Leaf(Printf.sprintf "%i" (List.length argst), inone);vabs], inone);(List.nth l pos)], inone);
                       fsigma vabs l
                   ], inone) in
                (pstr, types @ [t], put_equality, pos+1)
      | Some(nt, sigma) ->
         let add_sigma vabs l =
          Node(
          [
            Leaf("and", inone); 
            sigma (Node([Leaf("tuple_get", inone);Leaf(Printf.sprintf "%i" pos, inone); Leaf(Printf.sprintf "%i" (List.length argst), inone);vabs], inone)) (List.nth l pos);
            fsigma vabs l
          ], inone)
         in
         ((Printf.sprintf "%s%i" pstr pos), types @ [nt], add_sigma, pos+1)
      ) 
      (Printf.sprintf "%s_abs" pname, [], (fun _ _ -> Leaf("true", inone)), 0) argst 
    in
    (*let inst q c =
      let rec extract_from_sigma f =
        match 
      match c with
      | Node([Leaf("forall", _); Node([(Node([qname; qtype], _) as iq], _); Node([Leaf("=>", _);a;b], _) when iq = q ->
          match a with
          | 
          let v = unify (fsigma qname (List.mapi (fun i _ *)
          
          
      {predicate = p; 
            new_type = Leaf("test", inone); 
            suggested_npred = Node([Leaf(suggested,inone);Node([Leaf("->", inone); Node(Leaf("tuple", inone)::new_types, inone); Leaf("Bool", inone)], inone)], inone);
            fsigma = fsigma}::abss
            
  ) [] preds
  
let new_name suggested t =
  let open Tree in
  let n = ref 0 in
  let next_str () =
    let tmp = Printf.sprintf "%s_%i" suggested !n in
    n:= !n+1;
    tmp in
  let rec get_unique_name name =
    if Tree.leaf_exists (fun l i -> l = name) t then
      get_unique_name (next_str ())
    else name
    in
  get_unique_name suggested

let mk_quantifier bindertype q f =
  let open Tree in
  let inone = None in
  let Node([Leaf(qname, iq); qtype], _) = q in
  let n = ref 0 in
  let next_str () =
    let tmp = Printf.sprintf "%s_%i" qname !n in
    n:= !n+1;
    tmp in
  let rec get_unique_name name =
    if Tree.leaf_exists (fun l i -> l = name) (f (Leaf("_", iq))) then
      get_unique_name (next_str ())
    else name
    in
  let nq = Leaf(get_unique_name qname, iq) in
  Node([bindertype; Node([Node([nq; qtype], inone)], inone); f nq], inone)
  
let mk_quantifier2 bindertype q f =
  let open Tree in
  let inone = None in
  let Node([Leaf(qname, iq); qtype], _) = q in
  let n = ref 0 in
  let next_str () =
    let tmp = Printf.sprintf "%s_%i" qname !n in
    n:= !n+1;
    tmp in
  let rec get_unique_name name =
    if Tree.leaf_exists (fun l i -> l = name) (f (Leaf("_", iq))) then
      get_unique_name (next_str ())
    else name
    in
  let nq = Leaf(get_unique_name qname, iq) in
  (nq, Node([bindertype; Node([Node([nq; qtype], inone)], inone); f nq], inone))
      
let mk_forall n q f =
  mk_quantifier (Tree.Leaf("forall", n)) q f 

let mk_exists n q f =
  mk_quantifier (Tree.Leaf("exists", n)) q f 

let mk_forall2 n q f =
  mk_quantifier2 (Tree.Leaf("forall", n)) q f 

let mk_exists2 n q f =
  mk_quantifier2 (Tree.Leaf("exists", n)) q f 

let rec lift_tree f =
  let open Tree in
  match f with
  | Leaf(a, _) -> Leaf(a, None)
  | Node(l, _) -> Node(List.map lift_tree l, None)
  
let rec reduce_tree f =
  let open Tree in
  match f with
  | Leaf(a, _) -> Leaf(a, None)
  | Node(l, _) -> Node(List.map reduce_tree l, None)
  
let rec abstract_arrays abstraction f =
  let open Tree in
  (*Printf.eprintf "Abstracting : %s into %s\n" (print_tree abstraction.predicate) (print_tree abstraction.suggested_npred);*)
  Tree.rewrite_rec (fun t ->
    match t with
    | Node([Leaf("exists", _);Node([p], _); f], _) when p = abstraction.predicate -> 
        let Node([pname; Node([Leaf("->", _); Node(Leaf("tuple", _)::argst, _); Leaf("Bool", _)], _)], _) =  p in
        let Node([pabsname;Node([Leaf("->", _); Node(Leaf("tuple", _)::absargst, _); Leaf("Bool", _)], _)], _) = abstraction.suggested_npred in
        let fabs npredname = Tree.rewrite_rec (fun f ->
          match f with
          | Node(ppname::args, _) when ppname = pname-> 
              Some(mk_forall (Some(List.map reduce_tree args)) (Node(Leaf("vabs", None)::Node(Leaf("tuple", None)::absargst, None)::[], None)) (fun vabs -> 
              Node([Leaf("=>", None);abstraction.fsigma vabs args;
                               Node(npredname::(List.mapi (fun i t -> Node(
                                [Leaf("tuple_get", None);
                                Leaf(Printf.sprintf "%i" i, None); 
                                Leaf(Printf.sprintf "%i" (List.length absargst), None); 
                                vabs], None)) absargst), None)], None)))
          | _ -> None) f in
        Some(mk_exists None (abstraction.suggested_npred) fabs)
    | _ -> None) f
 

 let move_forall_forward f =
   let open Tree in
   let inone=None in
  Tree.rewrite_rec (fun t ->
    match t with
    | Node([Leaf("=>", _);a; Node([Leaf("forall", _); Node([q], _);f], _)], _) -> 
        let Node([qname;_], _) = q in
        let res = mk_forall inone q (fun qn -> Node([Leaf("=>", inone);a; if qn <> q then Tree.rewrite_rec (fun t -> if t = qname then  (if t = qn then None else Some(qn)) else None) f else f], inone)) in
        Some(res)
    | _ -> None) f
 
let rec mk_const t =
  let open Tree in
  match t with
  | Leaf("Int",_) -> Leaf("0",None)
  | Leaf("Bool",_) -> Leaf("true",None)
  | Node(Leaf("tuple", _)::q, _) -> Node(Leaf("mk_tuple", None)::(List.map mk_const q), None)
  | Node([Leaf("Array", _);a;b], _) -> Node([Leaf("as const", None);t;(mk_const b)], None)
  
let rec get_main_array e =
  match e with
  | Tree.Node([Tree.Leaf("store", _);a;b; c], _) -> get_main_array a
  | _ -> e
  
let instantiate_readset f =
  let open Tree in
  let inone=None in
  Tree.rewrite_rec (fun t ->
    match t with
    | Node([Leaf("=>", _);a; b], _) -> 
        let rdset = Tree.fold2 (fun _ -> []) (fun l t -> match t with 
                                                    | Node([Leaf("forall", _);Node([Node([qname; qtypes], _)], _);_], _) -> 
                                                        List.filter (fun (a,t) -> not (Tree.leaf_exists (fun l i -> (Leaf(l, i)) = qname) t)) (List.flatten l)
                                                    | Node([Leaf("select", _);a;b], _) -> (get_main_array a,b)::(List.flatten l)
                                                    | _ -> List.flatten l) t in
        (*if List.length rdset = 0 then failwith (Printf.sprintf "PROBLEM : Readset of size 0 !!! %s" (print_tree t));*)
        
        (*Printf.eprintf "rdset=%s\n\n" ((String.concat "\n" (List.map print_tree rdset)));*)
        Tree.rewrite_recopt (
          fun t ->  match t with 
                      | Node([Leaf("forall", Some(initargs));Node([Node([qname; Node(Leaf("tuple", _)::qtypes, _)], _)], _);f], _) -> 
                        
                        let initargs = List.map reduce_tree initargs in
                        let (instset,_) = List.fold_left (fun (sets, leftargs) t -> 
                          let linkedset = List.map snd (List.filter (fun (a,_) -> Tree.exists (fun abse -> abse = a) (List.hd leftargs)) rdset) in
                          let flinkedset = 
                            if List.length linkedset = 0 then 
                              match t with
                              | Node(Leaf("tuple", _)::a::b::[], _) -> 
(*                                                                     Printf.printf "%s" (print_tree (mk_const a));  *)
                                                                    [mk_const a] 
                              | _ -> []
                            else 
                              linkedset in
(*                           Printf.printf "Absvar : %s\nInitial rdset : %s\nFinal Rdset : %s\n\n" (print_tree (List.hd leftargs)) (String.concat "\n\t" (List.map (fun (a,b) -> Printf.sprintf "(%s, %s)" (print_tree a) (print_tree b)) rdset)) (String.concat "\n\t" (List.map print_tree linkedset)); *)
                          match t with
                          | Node(Leaf("tuple", _)::q, _) -> (*Printf.eprintf "Entering\n\n";*)
                            (List.flatten 
                              (List.map 
                                (fun s -> 
                                  List.map 
                                    (fun i -> 
                                     (* Printf.eprintf "reading %s\n\n" (print_tree i);*)
                                      s @ 
                                      [Node([Leaf("mk_tuple", None); i; Node([Leaf("select", None); List.hd leftargs;i], None)], None)]) flinkedset) sets)
                             , List.tl leftargs)
                          | _ -> (List.map (fun s -> s @ [List.hd leftargs]) sets, List.tl leftargs)) ([[]], (initargs)) qtypes in
                        let finstset = 
                          if List.length instset = 0 then
                            [List.map2 (fun t initv -> match t with 
                              | Node(Leaf("tuple", _)::a::b::[], _) -> let i = mk_const a in Node(Leaf("mk_tuple", None)::i::(Node([Leaf("select", None); initv;i], None))::[], None)
                              | _ -> initv) qtypes initargs]
                            
                          else
                          instset
                        in
                        let insts = List.map (fun inst -> Node(Leaf("mk_tuple", None)::inst, None)) finstset in
                          
                          
                        (*Printf.eprintf "instset=%s\n\n" ((String.concat "\n" (List.map print_tree insts)));*)
                        (*let mk_inst readval =
                          let (a,
                          let Node(Leaf("tuple", _)::types, _) = qtypes in
                          List.map (fun t -> match t with 
                                             | Node([Leaf("Array", _-); a; b]) -> Node([Leaf("mk_tuple", inone) ; readval; Node([Leaf("select", inone); 
                                             
                                    )types*)
                        Some(Node(
                          Leaf("and", inone)::
                          (List.map (fun inst -> Tree.rewrite_rec (fun t -> if t = qname then Some(inst) else None) f) insts), inone))
                          
                      | _ -> None) t 
    | _ -> None) f
 
let rewrite_tuples_as_pairs f =
  let open Tree in
  let inone=None in
  Tree.rewrite_rec (fun t ->
    match t with
    | Node(Leaf("tuple", _)::l, _) -> 
        begin
        match l with
        | [] -> failwith "empty tuple"
        | [a] -> failwith "tuple of one element"
        | [a;b] -> Some(Node([Leaf("Pair", inone); a; b], inone))
        | a::q -> Some(Node([Leaf("Pair", inone); a; Node(Leaf("tuple", inone)::q, inone)], inone))
        end
    | Node([Leaf("tuple_get", _);Leaf(i, _);Leaf(n, _);t], _) -> 
        begin
        let i = int_of_string i in
        let n = int_of_string n in
        let rec get_as_pair i n t =
          if i = 0 then Node([Leaf("fst", inone);t], inone)
          else if n = 2 then Node([Leaf("snd", inone);t], inone)
          else get_as_pair (i-1) (n-1) (Node([Leaf("snd", inone);t], inone))
        in
        Some(get_as_pair i n t)
        (*else Node([Leaf("snd", inone);Node([Leaf("tuple_get", inone);Leaf(string_of_int (i-1), inone);Leaf(string_of_int (n-1), inone);t], inone)], inone)*)
        end
    | Node(Leaf("mk_tuple", _)::a::b::[], _) -> Some(Node(Leaf("mk-pair", None)::a::b::[], None))
    | Node(Leaf("mk_tuple", _)::a::b::q, _) -> Some(Node(Leaf("mk-pair", None)::a::(Node(Leaf("mk_tuple", None)::b::q, None))::[], None))
    | _ -> None) f
  
let rec mfind_map f l =
  match l with
  | [] -> None
  | a::q when f a = None -> mfind_map f q
  | a::q -> f a

let simplify_expr f =
  let open Tree in
  let inone=None in
  
  let rewrite_pair_foralls t =
    match t with 
    | Node([Leaf("forall", _); Node(ql, _); f], _) ->
       let (nqs, replaces) = List.fold_left (fun (nqs, replaces) q  ->
        match q with
        | Node([(Leaf(qn, _)) as mq ; Node([Leaf("Pair", _);a;b], _)], _) -> 
            let nw1 = new_name (Printf.sprintf "%s_f" qn) t in
            let nw2 = new_name (Printf.sprintf "%s_s" qn) t in
            if nw1 =nw2 then failwith "error equal names";
            let nq1 = Leaf(nw1, None) in
            let nq2 = Leaf(nw2, None) in
            (nqs @ [Node([nq1; a], None);Node([nq2; b], None)], (mq, (nq1, nq2))::replaces)
        | _ -> (nqs @ [q], replaces)) ([], []) ql
        in
        (*Printf.eprintf "New quantifiers : %s\n" (String.concat " " (List.map print_tree nqs));*)
        let nf = Tree.rewrite_rec (fun t-> if List.mem_assoc t replaces then let (t1, t2) = List.assoc t replaces in Some(Node([Leaf("mk-pair", None);t1;t2], None)) else None) f in
      Node([Leaf("forall", None); Node(nqs, None); nf], None) 
      in
  
  Tree.rewrite_rec (fun t ->
  match t with
    (*Removes useless equalities*)
    | Node([Leaf("=", _); a;b], _) when a =b -> Some(Leaf("true", None))
    (*Decurifies*)
    | Node([Leaf("=>", _); a; Node([Leaf("=>", _); b; c], _)], i) -> Some(Node([Leaf("=>", None); Node([Leaf("and", inone); a;b], inone); c], None))
    (*Removes useless implications*)
    | Node([Leaf("=>", _); Leaf("true",_); a], _) -> Some(a)
    | Node([Leaf("=>", _); Leaf("false",_); a], _) -> Some(Leaf("true", None))
    | Node([Leaf("=>", _); a; Leaf("false",_)], _) -> Some(Node([Leaf("not", None);a], None))
    | Node([Leaf("=>", _); a; Leaf("true",_)], _) -> Some(Leaf("true", None))
    (*Remove useless stuff in ands and useless ands*)
    | Node(Leaf("and", _)::l, _) -> 
       begin
       let all_ands = List.flatten (List.map
         (fun e -> match e with
         | Node(Leaf("and", _ )::l2, _) -> l2
         | _ -> [e]) l )
       in
       let true_rm = List.filter (fun t -> match t with Leaf("true", _) -> false | _ -> true) all_ands in
       let res = match true_rm with
       | [] -> Leaf("true", None)
       | [a] -> a
       | _ ->  Node(Leaf("and", None)::true_rm, None) in 
      if res=t then None else Some(res)
      end
    (*Removes quantifiers used in formula of the form q = a => f*)   
    | Node([Leaf("forall", _); Node(ql, _); (Node([Leaf("=>", _); Node(([Leaf("=", _); _;_]) as eqs, _); f], _)) as bigf], _) 
    | Node([Leaf("forall", _); Node(ql, _); (Node([Leaf("=>", _); Node(Leaf("and", _)::eqs,_); f], _)) as bigf], _) 
        -> let (qleft, replaces) = 
             List.fold_left 
              (fun (qleft, replaces) q ->
                let Node([qn; _], _) = q in
                if List.exists (fun (q, r) -> Tree.exists (fun x -> x= qn) r) replaces then (qleft @ [q], replaces) 
                else
                let replace = mfind_map (fun eq -> match eq with
                                      | Node([Leaf("=", _); a;b], _) when a = qn -> if Tree.exists (fun x -> x= qn) b then None else Some(b)
                                      | Node([Leaf("=", _); a;b], _) when b = qn -> if Tree.exists (fun x -> x= qn) a then None else Some(a)
                                      | _ -> None) eqs in
                match replace with
                | None -> (qleft @ [q], replaces) 
                | Some(x) -> (qleft, (qn, x)::replaces)
              ) ([], []) ql in
            let res = 
              rewrite_pair_foralls (Node([Leaf("forall", None); Node(qleft, None); Tree.rewrite_rec (fun t -> if List.mem_assoc t replaces then Some( List.assoc t replaces) else None) bigf], None)) in 
            if res=t then None else Some(res)
            
    (*Simplifies pairs*)
    | Node([Leaf("forall", _); Node(ql, _); f], _) -> let res = rewrite_pair_foralls t in if res=t then None else Some(res)
       (*let (nqs, replaces) = List.fold_left (fun (nqs, replaces) q  ->
        match q with
        | Node([(Leaf(qn, _)) as mq ; Node([Leaf("Pair", _);a;b], _)], _) -> 
            let nw1 = new_name (Printf.sprintf "%s_f" qn) t in
            let nw2 = new_name (Printf.sprintf "%s_s" qn) t in
            if nw1 =nw2 then failwith "error equal names";
            let nq1 = Leaf(nw1, None) in
            let nq2 = Leaf(nw2, None) in
            (nqs @ [Node([nq1; a], None);Node([nq2; b], None)], (mq, (nq1, nq2))::replaces)
        | _ -> (nqs @ [q], replaces)) ([], []) ql
        in
        let nf = Tree.rewrite_rec (fun t-> if List.mem_assoc t replaces then let (t1, t2) = List.assoc t replaces in Node([Leaf("mk-pair", None);t1;t2], None) else t) f in
      Node([Leaf("forall", None); Node(nqs, None); nf], None) *)
      
    (*| Node([Leaf("forall", _); Node([Node([a;Node([Leaf("Array"); indt; valt], _)], _) ], _); f], _) -> 
        let rec opwitha t =
          match t with
          | Node([Leaf("select", _); ar; i], _) when ar=a -> ([],[i])
          | Node([Leaf("forall"); [qs];fs], _) -> 
            let tmp = opwitha fs in*)
            
    
    
    | Node([Leaf("fst", _); Node([Leaf("mk-pair", _);a;b], _)], i) -> Some(a)
    | Node([Leaf("snd", _); Node([Leaf("mk-pair", _);a;b], _)], i) -> Some(b)
    | Node([Leaf("mk-pair", _); Node([Leaf("fst", _);a], _);Node([Leaf("snd", _);b], _)], i) when a = b-> Some(a)
    | Node([Leaf("SEQ", _); Node([Leaf("declare-fun", _); pname; Node(argstypes, _); ret], _); f], _) ->
        let (positions, nt, _) = 
           List.fold_left (fun (pos, nt, i) e -> match e with  Node([Leaf("Pair", _);a;b], _) -> (pos @ [true], nt @ [a;b], i+1) | _ -> (pos @ [false], nt @ [e], i+1)) ([], [], 0) argstypes in
        if List.length positions = 0 then None else 
        begin
        let f2 = Tree.rewrite_rec (fun t -> match t with
                             | Node(_, Some(Leaf("tmp", None))) -> None
                             | Node(p::l, _) when p = pname -> 
                               (if List.length l <> List.length positions then Printf.eprintf "error length %i %i %i " (List.length l) (List.length positions) (List.length argstypes)) ;
                               Some(Node(p::(List.flatten (List.map2 (fun e b -> if b then [Node([Leaf("fst", None); e], None); Node([Leaf("snd", None); e], None)] else [e]) l positions)), Some(Leaf("tmp", None))))
                             | _ -> None) f in
        let res = Node([Leaf("SEQ", None); Node([Leaf("declare-fun", None); pname; Node(nt, None); ret], None); f2], None) in 
        if res=t then None else Some(res)
        end
    | _ -> None) f
    
let group_forall f = 
  let open Tree in
  Tree.rewrite_rec (fun t ->
  match t with
    | Node([Leaf("forall", _);(Node(qs1, _));Node([Leaf("forall", _);(Node(qs2, _)); f], _)], _) -> Some(Node([Leaf("forall", None);(Node(qs1 @ qs2, None)); f], None))
    | _ -> None) f

(*let rec remove_pairs f =
  let open Tree in
  let inone=None in
  Tree.rewrite_rec (fun t -> 
  match t with
    | Node([Leaf("forall", _);(Node(qs1, _));Node([Leaf("forall", _);(Node(qs2, _)); f], _)], _) -> Node([Leaf("forall", None);(Node(qs1 @ qs2, None)); f], None)
    | _ -> t) f*)
    
let add_z3_instructions f =
  let open Tree in
  Node([Leaf("SEQ", None); 
         Leaf("(set-logic HORN)", None) ; 
         Node([Leaf("SEQ", None);
             f;
             Leaf("(check-sat)", None) 
            ], None)
         ], None) 


         
let rec ackermanize f = 
    let open Tree in
    Tree.rewrite_rec (fun tinit ->
      match tinit with 
      | Node([Leaf("forall", _); Node(ql, _); t], _) ->
        let t = Tree.rewrite_rec (fun t -> match t with | Node([Leaf("select", _);Node([Leaf("store", _);  a  ;  i  ;  v ], _); j], None) -> 
                                                            Some(Node([Leaf("ite", None); Node([Leaf("=", None);i ; j], None)  ;  v ; Node([Leaf("select", None);a ; j],None) ], None))
                                                        | _ -> None) t in
        let (keepq, rmq) = List.partition (fun q ->
                                             match q with 
                                               | Node([qstr; Node([Leaf("Array", _);a;b], _)], _) -> 
                                                    (Tree.exists (fun e -> match e with 
                                                                     | Node(l, _) when (List.exists (fun x -> x=qstr) l) && (List.hd l <> Leaf("select", None)) -> true 
                                                                     | Node(l, _) -> false
                                                                     | _ -> false) 
                                                           t)
                                               | _ -> true
                                             
                                      ) ql in
                                      
(*         Printf.printf "Removing : %s\n\n" (String.concat " " (List.map print_tree rmq));                               *)
        let rec rmselects q createdq expr =
          let rec find_select e = 
            match e with
            | Leaf(_,_) -> None
            | Node([Leaf("select", _); a; _],_) when a = q -> Some(e)
            | Node(l, _) -> List.fold_left (fun o x -> match o with | Some(_) -> o | _ -> find_select x) None l in
          match find_select expr with
          | Some(s) -> 
            let Node([Leaf("select", _); _; i],_) = s in
            let nq = Leaf(new_name (Printf.sprintf "%s_select" (print_tree q)) expr, None) in
            let e_with_eq = Node([Leaf("=>", None);Node(Leaf("and", None)::(List.map (fun (qstr, ind) ->  
              Node([Leaf("=>", None);Node([Leaf("=", None); i; ind], None);Node([Leaf("=", None); qstr;nq], None)], None)) createdq), None); expr], None) in
            let new_e = Tree.rewrite_rec (fun t -> if t=s then Some(nq) else None) e_with_eq in
            rmselects q ((nq, i)::createdq) new_e
          | None -> (createdq, expr) in
        
        
        let (newvars, newt) = 
          List.fold_left (fun (newvars, newt) q ->
            let Node([qstr; Node([Leaf("Array", _);_;desttype], _)], _) = q in
            let (nqs, new_e) = rmselects qstr [] newt in
            (newvars @ List.map (fun nq -> Node([nq; desttype], None)) (List.map fst nqs), new_e)) ([], t) rmq in
            
            
          
        (*let selectsq = 
          List.map
          (
            fun q -> 
              let Node([qstr; _], _) = q in
              let selects = Tree.fold2 
              (fun _ -> []) 
              (fun se t -> match t with | Node([Leaf("select", _); a; i],_) when a = qstr -> t::(List.flatten se) | _ -> (List.flatten se))
              t in
              (List.fold_left (fun se s -> if List.exists (fun x -> x =s) se then se else s::se) [] selects)
          ) 
          rmq in
        let (newvars, newt) = 
          List.fold_left2 
            (fun (nv, nt) q selects ->  
              let (qstr, dtype) = match q with
                | Node([(Leaf(qstr, _)); Node([Leaf("Array", _);a;b], _)], _) -> (qstr, b)
                | _ -> failwith "should not happend due to partition" in
              let (nvq, ntq) =
                List.fold_left 
                (
                  fun (nvq, ntq) s -> 
                    let Node([Leaf("select", _); _; i],_) = s in
                    let nw = new_name (Printf.sprintf "%s_select" qstr (*(String.get (print_tree i) 0)*)) ntq in
                    let nq = Node([Leaf(nw, None); dtype], None) in
                    let eqs = List.map (
                               fun (q, ind) -> 
                                 let Node([qstr; _], None) = q in 
                                 Node([Leaf("=>", None);Node([Leaf("=", None); i; ind], None);Node([Leaf("=", None); qstr; Leaf(nw, None)], None)], None)
                               ) nvq in
                    let rewritten = Tree.rewrite_rec (fun t -> if t=s then Some(Leaf(nw, None)) else None) ntq in
                    ((nq, i)::nvq, Node(Leaf("and", None)::rewritten::eqs, None))
                ) ([], nt) selects in
              (nv @ (List.map fst nvq), ntq)
         
            ) ([], t) rmq selectsq in*)
          let res = Node([Leaf("forall", None); Node(keepq @ newvars, None); newt], None) in
          if res=tinit then None else Some(res)
    |  _ -> None
    ) (reduce_tree f)
    
    
let _  =
  (*Show where exceptions comme from*)
  Printexc.record_backtrace(true);

  try
    (*Read arguments*)
    let cf = read_args() in

    (*Only show where expressions come from and show filename when debug is activated*)
    Printexc.record_backtrace(false);
    if cf.debug then Printf.printf "File is %s\n" cf.f_name;

    (*Retrieving program in as expressions. Nothing is interpreted yet*)
(*     Printf.eprintf "started\n"; *)
    let horn = parse cf in
(*     Printf.eprintf "parsed\n"; *)
    (*if cf.debug then Printf.printf "Printing parsed expression :\n%s\n\n\n" (printHorn horn);*)
    let horn2 = as_formula (lift_tree horn) in
    
    (*Printf.eprintf "\n\nDEBUG formula : \n %s" (print_tree horn2);*)
    
    let array_abss =  mk_abstractions (fun t -> let open Tree in
                                                let inone=None in
                                                match t with 
                                               | Node([Leaf("Array", _);a;b], _) -> 
                                                 Some(Node([Leaf("tuple", inone); a; b], inone), fun v arg -> 
                                                     let i = Node([Leaf("tuple_get", inone); Leaf("0", inone); Leaf("2", inone);v], inone) in
                                                     let v = Node([Leaf("tuple_get", inone); Leaf("1", inone); Leaf("2", inone);v], inone) in
                                                     Node([Leaf("=", inone); v; Node([Leaf("select", inone); arg;i], inone)], inone)
                                                 )
                                               | _ -> None) (get_preds horn2) in
(*     Printf.eprintf "mkabs"; *)
    
    let abstracted = (List.fold_left (fun h abss -> abstract_arrays abss h) (lift_tree horn2) array_abss) in
(*     Printf.eprintf "abs"; *)
    let moved_forward = move_forall_forward abstracted in
(*     Printf.eprintf "mv"; *)
    (*failwith (Printf.sprintf "%s" (print_tree (from_formula moved_forward)));*)
    let instantiated = reduce_tree (instantiate_readset moved_forward) in
(*     let tmp = (simplify_expr (rewrite_tuples_as_pairs (from_formula instantiated))) in *)
    let simplified = group_forall (simplify_expr (rewrite_tuples_as_pairs (from_formula instantiated))) in
    
    let possibly_ackermanised = if cf.acker then group_forall (simplify_expr (ackermanize simplified)) 
                                else simplified in
    (*failwith "inst";*)
    let str_final = (*Printf.sprintf "parsed: \n%s\n\nrewritten : \n%s\n\nabstracted : \n%s\n\nabs rewritten :\n%s\n\nmoved_forward :\n%s\n\ninstantiated :\n%s\n\ntuples rewritten : \n%s\n\nsimplified:\n%s\n\ngrouped_forall + z3 inst :\n%s" 
      (print_tree horn2)
      (print_tree (from_formula horn2))
      (print_tree abstracted)    
      (print_tree (from_formula abstracted))  
      (print_tree (from_formula moved_forward)) 
      (print_tree (from_formula instantiated)) 
      (print_tree (rewrite_tuples_as_pairs (from_formula instantiated))) 
      (print_tree (simplify_expr (rewrite_tuples_as_pairs (from_formula instantiated)))) 
      (print_tree (add_z3_instructions (group_forall (simplify_expr (rewrite_tuples_as_pairs (from_formula instantiated))))))*)
(*       Printf.sprintf "%s" (print_tree (add_z3_instructions (group_forall (simplify_expr (rewrite_tuples_as_pairs (from_formula ackermanised)))))) *)
      Printf.sprintf "%s" (print_tree (add_z3_instructions possibly_ackermanised))
      in
    
    
    (*We interpret variables, asserts, function declarations, foralls, ...*)
    (*let converted = mapHorn interpretExpr horn in
    if cf.debug then Printf.printf "Printing converted expression :\n%s\n\n\n" (printHorn converted);
    
    
    let datatypesadded=
    {command=Some(Interpreted("(set-logic HORN)")); comment=";adding solving logic"}::
    {command=Some(Interpreted("(declare-datatypes (T1 T2) ((Pair (mk-pair (fst T1) (snd T2)))))")); comment=";adding pair datatype"}::
    (List.filter (fun c -> match c with {command = Some(Apply(Interpreted("set-logic"), l)); comment=_} -> false | _ -> true) converted) in
    
    let abstracted = allabs (fun _ t _ -> match t with 
                               | Apply(Interpreted("Array"), a::b::[]) -> 
                                 Some((fun expr var -> 
                                   Apply(Interpreted("="), Apply(Interpreted("snd"), var::[])::Apply(Interpreted("select"), expr::Apply(Interpreted("fst"), var::[])::[])::[])), Apply(Interpreted("Pair"), a::b::[]))
                               | e -> None
                            ) datatypesadded in
                            
                            
    let instantiated = instHorn (fun context var t e -> 
      let ctx = context (Interpreted("_")) in
      let rec get_tail expr =
        match expr with
        | Interpreted("_") -> expr
        | Apply(Interpreted("=>"), [Apply(Interpreted("and"), []); r]) -> get_tail r
        | Apply(Interpreted("=>"), [Apply(Interpreted("and"), Interpreted("_")::q); r]) -> expr
        | Apply(Interpreted("=>"), [Apply(Interpreted("and"), a::q); r]) -> get_tail (Apply(Interpreted("=>"), [Apply(Interpreted("and"), q); r]))
        | Apply(Interpreted("=>"), [a; r]) -> get_tail (Apply(Interpreted("=>"), [Apply(Interpreted("and"), [a]); r]))
        | _ -> expr in
        
      Some(match readset (get_tail ctx) with 
      | [] -> ([ExpressionList([var;t])], [var]) 
      | l -> match e with
        | Apply(Interpreted("=>"), [Apply(Interpreted("="), Apply(Interpreted("snd"), v::[])::Apply(Interpreted("select"), expr::Apply(Interpreted("fst"), v2::[])::[])::[]); predicate]) -> 
        ([], List.map (fun ind -> Apply(Interpreted("mk-pair"), [ind; Apply(Interpreted("select"), [expr;ind])])) l)
        | _ -> Printf.eprintf "Expression is : %s" (printExpr e); failwith "non abstraction instantiation error"
    )) abstracted in
    
    let simplified = toHornFormat instantiated in
    (*let abstracted = hornabs "assign" {fname="assignabs";params=Parametrized(Basic("Array")::Basic("Int")::Basic("Int")::[])::Basic("Int")::[];return=Basic("Bool")} 0 (fun c a -> Composition(Interpreted("=")::c::a::[])) converted in*)
(*
    (*Abstraction we use*)
    let mabstraction = absdistinctsize (cf.distinct_i) in

    (*We now retrieve the abstract operations and we apply alpha (the abstraction for types) *)
    let transformed = (transformHorn mabstraction converted) in
    if cf.debug then Printf.printf "Printing transformed expression :\n%s\n\n\n" (printHorn transformed);
    
    (*Now that we know the abstract operations, we can normalize the expression*)
    let normalized = hornNormalize mabstraction transformed in
    if cf.debug then Printf.printf "Printing normalized expression :\n%s\n\n\n" (printHorn normalized);
    
    (*We now abstract the operations*)
    let abstracted = abstractHorn mabstraction normalized in
    if cf.debug then Printf.printf "Printing abstracted expression :\n%s\n\n\n" (printHorn abstracted);

    (*We finally simplify the expression (consists in removing the tuples)*)
    let final = remove_tuples abstracted in
    if cf.debug then Printf.printf "Printing tuple removed expression :\n%s\n\n\n" (printHorn final);
    
    *)
    
    (*Getting simplified horn string*)
    let str_final = (printHorn simplified) in
    if cf.debug then Printf.printf "Printing final expression :\n%s\n\n\n" str_final;*)
    if cf.outputsmt_name = "stdout" then 
      Printf.printf "%s" str_final
    else
      let outfile = open_out cf.outputsmt_name in
      Printf.fprintf outfile "%s" str_final;
  with
    (*Whenever an exception is thrown, print expression and backtrace (empty if debug = false), and exit with -1 status*)
    | e -> Printf.printf "\n\nException : %s %s\n\n" (Printexc.to_string e) (Printexc.get_backtrace ()); exit (-1)



