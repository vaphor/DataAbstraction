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

(*A generic tree type where inner nodes and leaf may not contain the same information*)

module Tree = 
  struct 
    type ('node_info, 'leaf_info) tree = Leaf of 'leaf_info | Node of (('node_info, 'leaf_info) tree) list * 'node_info
    let rec fold fleaf fnode t =
      match t with
      | Leaf(i) -> fleaf i
      | Node(l, i) -> fnode (List.map (fold fleaf fnode) l) i
      
    let rec fold2 fleaf fnode t =
      match t with
      | Leaf(i) -> fleaf i
      | Node(l, i) -> fnode (List.map (fold2 fleaf fnode) l) t
      
      
    (*let rec one_step f t =
      let rec change_first l =
        match l with
        | [] -> []
        | a::q -> match one_step f a with | None -> a::(change_first q) | Some(x) -> x::q
      in
      match (f t, t) with
      | (None, Leaf(_,_)) -> None
      | (None, Node([],_)) -> None
      | (None, Node(a::q,i)) -> Node(change_first l, i)*)
      
    let rec rewrite_recn n f t =
    if n = 0 then failwith "too many rewrites";
    let app = f t in
    let next = 
      if app = t then
        match t with
        | Leaf(_,_) -> t
        | Node(l,i) -> Node(List.map (rewrite_recn (n-1) f) l , i)
      else
        app in
    if next = t then t else rewrite_recn (n-1) f next
    
    let rec rewrite_recopt f t =
      let rec rw_list l = 
        match l with
        | [] -> None
        | a::q -> begin match (rewrite_recopt f a,  rw_list q) with
                   | None, None -> None
                   | Some(b), None -> Some(b::q)
                   | None, Some(r) -> Some(a::r)
                   | Some(b), Some(r) -> Some(b::r)
                end in
                            
     let res = match f t with
     | Some(t2) -> (*if t2=t then failwith (Printf.sprintf "error infinite loop : %s" (print t)) else begin*) (match rewrite_recopt f t2 with | None -> Some(t2) | Some(x) -> Some(x))
     | None -> 
        begin
          match t with
          | Leaf(_, _) -> None
          | Node(l, id) -> match rw_list l with
                           | None -> None
                           | Some(x) -> let r = Node(x, id) in
                                        match rewrite_recopt f r with None -> Some(r) | Some(o) -> Some(o)
        end
      in
      (*Printf.eprintf "Input = \n%s\nResult = \n%s\n\n" (print t) (match res with None -> "nochange" | Some(res) -> print res);*)res
    (*  let next =
        match f t with
        | Leaf(_,_) -> f t
        | Node(l,i) -> Node(List.map (rewrite_recn (n-1) f) l , i)
      in
      if next = t then t else rewrite_recn (n-1) f next*)
      
      let rewrite_rec f t = match rewrite_recopt f t with None -> t | Some(x) -> x
    (*let rec rewrite_rec f t = rewrite_recn 1000 f t*)
     (* let next =
        match f t with
        | Leaf(_,_) -> f t
        | Node(l,i) -> Node(List.map (rewrite_rec f) l , i)
      in
      if next = t then t else rewrite_rec f next*)
      
    let rec leaf_exists f t =
      match t with
      | Leaf(l, i) -> f l i
      | Node(l, i) -> List.exists (fun x -> leaf_exists f x) l
      
    let rec exists f t =
      if f t then true else
      match t with
      | Leaf(l, i) -> false
      | Node(l, i) -> List.exists (fun x -> exists f x) l
  end

  
(*module type ExprSymbols =
  sig
    type symbol
    val is_binder : symbol -> bool
    val none : symbol
  end*)
  
module StrSymbols =
  struct
    type symbol = string
    let is_binder str = match str with "forall" | "exists" -> true | _ -> false
    let none = "_"
  end
  
(*Information needed on nodes to help expression handling*)
(*module type ExprInfoType =
   sig
     type symbol
     type info
     type tree = (info, (symbol * info)) Tree.tree
     
     val none : info
     
     (*val add_type_info: tree -> info  -> info
     val get_type_info: info -> tree option
     val rm_type_info: info -> info
     
     val set_old_used_variable: tree -> info -> info
     val get_old_used_variable: tree -> info -> info
     val rm_old_used_variable: info -> info
     
     val has_free_variable:  tree -> info -> bool
     val add_free_variable: tree -> info -> info
     val rm_free_variable: tree -> info -> info  *)
   end*)

module Info =
  struct
    type symbol = string
    type info = unit
    type tree = (info, (symbol * info)) Tree.tree
    let none = ()
  end

(*
(*Provides an "expression view" of a tree*)
module Expr = functor (Symbols : ExprSymbols) (Info: ExprInfoType with type symbol = Symbols.symbol)  -> 
  struct
    (*This should be the same as Symbols.symbol*)
    type symbol = Info.symbol
    type info = Info.info
    type tree = Info.tree
    type expr_view =
      | Symbol of symbol * (symbol -> tree)
      | Apply of tree * tree list * (tree -> tree list -> tree)
      | Var of symbol * (symbol -> tree)
      | Binder of tree (*forall, exists, fun , ...*) *  tree (*type expression*) * (tree -> tree) (*var -> expression*) * (tree -> tree -> (tree->tree) -> tree)
    
    open Tree
    
    let replace_in from by t = failwith "not done"
    let set_name var fe = failwith "not done"
    let empty = Leaf(Symbols.none, Info.none)
      (*Constructs the expression view of a tree*)
    let rec to_expr_view tree = 
      match tree with   
      | Leaf(s, i) -> Symbol(s, fun s -> Leaf(s, i))
       
        (*The empty binder case...*)
      | Node([Leaf(binder, i0);Node([], i1);e], i2) when Symbols.is_binder binder -> 
          begin
          let ctr_from_e e = Node([Leaf(binder, i0);Node([], i1);e], i2) in
          match to_expr_view e with
          | Symbol(s, ctr) | Var(s, ctr) -> Symbol(s, fun s -> ctr_from_e (ctr s))
          | Apply(t,l,ctr) -> Apply(t,l, fun t l ->  ctr_from_e (ctr t l))
          | Binder(q,t, ef, ctr) -> Binder(q,t, ef, fun q t ef ->  ctr_from_e (ctr q t ef))
          end
          
        (*The one binder case*)   
      | Node([Leaf(binder, i0);Node([Node([v;t], ivar)], i1);e], i2) when Symbols.is_binder binder -> 
          Binder(
             Leaf(binder, i0), 
             t, 
             (fun var -> replace_in v var e), 
             fun b t fe -> 
               Node([b;Node([Node([v;t], ivar)], i1);set_name v fe], i2)
          )
      
      (*The multiple binder case*)   
      | Node([Leaf(binder, i0);Node(Node([v;t], ivar)::q, i1);e], i2) when Symbols.is_binder binder -> 
          let newe e = Node([Leaf(binder, i0);Node(q, ivar); e], i2) in
          Binder(
             Leaf(binder, i0), 
             t, 
             (fun var -> replace_in v var (newe e)), 
             fun b t fe -> 
               match (fe empty, b) with
               | (Node([Leaf(fbinder, fi0);Node([Node(fq, fivar)], fi1);ne], fi2), Leaf(fb, fi)) when 
                    ((fbinder = binder) && (fb = binder) && ((List.length fq) = (List.length q))) ->
                  Node([b;Node(Node([v;t], ivar)::fq, i1);set_name v 
                  (
                    fun var -> match (fe var, b) with
                      | (Node([Leaf(fbinder, fi0);Node([Node(fq, fivar)], fi1);ne], fi2), Leaf(fb, fi)) when 
                          fbinder= binder && fb = binder && List.length fq = List.length q ->
                         ne
                      | _ -> failwith "You are messing up with caml functions that should only represent expressions..."
                  )], i2)
               | _ -> Node([b;Node([Node([v;t], ivar)], i1);set_name v fe], i2)
          )
          
      | Node(Leaf(binder, _)::q, _) when Symbols.is_binder binder -> failwith "Wrong binder definition"     
      | Node(f::l, i) -> Apply(f,l, fun f l -> Node(f::l, i))    
      | Node([],_) -> failwith "What are you doing ?!"  
          
          
 (* | Node([binder;Node([Node([v;t])]);e], i) when is_binder binder -> 
    let new_expr var_expr = 
      match var_expr.etype with
      | None -> replace_in v ({var_expr with etype=Some(t)}) e
      | Some(typ) when typ = t -> replace_in v var_expr e
      | Some(_) -> failwith "Error while matching types" 
    in
    Binder(binder, t, new_expr, i)
  
  | Node([binder;Node(Node([v; t])::q);e], i) when is_binder binder -> 
    let new_binder = {binder with attributes = ("old_quantifier_variable", v_name)::binder.attributes in
    let new_expr var_expr = 
      match var_expr.etype with
      | None -> replace_in v ({var_expr with etype=Some(t)}) e
      | Some(typ) when typ = t -> Node([binder; Node([q]);  replace_in v var_expr e])
      | Some(_) -> failwith "Error while matching types" 
    in
    Binder(new_binder, t, new_expr, i)
    
  | Node(binder::_, _) when is_binder binder -> failwith "Error while matching binder" 
  | Node(f::args, i) -> Apply(f, args, i)
  | Node(_) -> failwith "Empty node"
      match t with 
        | Leaf(s, i) -> Symbol(s, fun s -> Leaf(s, i))
        | Node(a::q, i) -> Apply(a, q, fun a q -> Node(a::q, i))
        | _ -> failwith "error"
    
    (*val from_expr_view : tree -> expr_view*)*)
  end

  
module Test = Expr(StrSymbols)(Info)


*)

(*module basic_info =
  struct 
    type tree 

type parsed_view =
      | Select of tree * tree * (tree -> tree -> tree)
      | Store of tree * tree * tree * (tree -> tree -> tree -> tree)
      | Forall of tree (*the type*) * (tree -> tree) * (tree -> (tree->tree) -> tree)
      | Exists of tree (*the type*) * (tree -> tree) * (tree -> (tree->tree) -> tree)
      | Other of tree * (tree -> tree)


  



and parsed_view =
  | Select of tree * tree * info
  | Store of tree * tree * tree * info
  | Forall of tree (*the type*) * info
  | Exists of tree * (tree -> tree) * info
  | Solver of tree * info

and problem = tree list

and formula_view =
{
  expr : tree
  reconstruct : tree -> problem
}

and horn_view =
{
  preds_types : tree list;
  clauses : tree list (*preds name*) -> clause list;
  reconstruct : tree list -> clause list -> problem;
}

and clause =
{
  var_types : tree;
  premise : tree list (*vars*) -> tree;
  next : clause;
}

let add_tree_attribute t key str =
  match t with 
  | Leaf(e, i) -> 
    if List.mem_assoc key i then 
      failwith "Key already exists in info"
    else
      Leaf(e, i::(key, str))
  | Node(l, i) -> 
    if List.mem_assoc key i then 
      failwith "Key already exists in info"
    else
      Node(l, i::(key, str))

let add_string_attribute t key str =
  add_tree_attribute t key (Leaf(str))
  
let get_tree_attribute t key =
  match t with
  | Leaf(_, i) | Node(_, i) -> 

(*tree -> expr_view *)
let rec to_expr_view ctx_vars t =
  let is_binder e = match e with
    | Leaf("forall", _) -> true
    | Leaf("exists", _) -> true
    | _ -> false
  in
  match t with   
  | Leaf(str. i) -> Symbol(str, i)
    
  | Node([binder;Node([]);e], i) when is_binder binder -> 
    (*What to do with info on binder and on this expression ?*)
    to_expr_view ctx_vars e
    
  | Node([binder;Node([Node([v;t])]);e], i) when is_binder binder -> 
    let new_expr var_expr = 
      match var_expr.etype with
      | None -> replace_in v ({var_expr with etype=Some(t)}) e
      | Some(typ) when typ = t -> replace_in v var_expr e
      | Some(_) -> failwith "Error while matching types" 
    in
    Binder(binder, t, new_expr, i)
  
  | Node([binder;Node(Node([v; t])::q);e], i) when is_binder binder -> 
    let new_binder = {binder with attributes = ("old_quantifier_variable", v_name)::binder.attributes in
    let new_expr var_expr = 
      match var_expr.etype with
      | None -> replace_in v ({var_expr with etype=Some(t)}) e
      | Some(typ) when typ = t -> Node([binder; Node([q]);  replace_in v var_expr e])
      | Some(_) -> failwith "Error while matching types" 
    in
    Binder(new_binder, t, new_expr, i)
    
  | Node(binder::_, _) when is_binder binder -> failwith "Error while matching binder" 
  | Node(f::args, i) -> Apply(f, args, i)
  | Node(_) -> failwith "Empty node"
  
  
let from_expr_view expr = 
  match expr with
  | Symbol(str, i) -> Leaf(str, i)
  | Var(str, i) -> Leaf(str, i)
  | Apply(f, args, i) -> Node(f, args, i)
  | Binder(binder, t, fe, i) -> let suggested_var_name = List.assoc "old_quantifier_variable" Node(binder, Node())
  
(*| Leaf(str, i) when List.exists (fun (v, _) -> v = str) ctx_vars -> 
    let t = List.assoc str ctx_vars in 
    match i.etype with
    | None -> Var(str, {i with etype = Some(t)})
    | Some(typ) when t=typ -> Var(str, i)
    | Some(_) -> failwith "Error while matching types"*)

(*let default 
  
  
  to_expr_view_with_ctx ctx_vars e

(* expr_view -> tree *)
let from_expr_view expr =
  match expr 
val from_parsed_view : parsed_view -> tree*)

*)
