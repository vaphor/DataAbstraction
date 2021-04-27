

open Expr
open Horn

module Insts_set = Set.Make (struct type t = expr*expr let compare = compare end)
type insts_set = Insts_set.t

type abstraction =
{
  name : string;
  concrete_type : expr;
  abstract_type : expr;
  fsigmaq : expr (*quants*) -> expr -> expr -> expr;
  fsigma : expr -> expr -> expr;
  insts : expr -> expr -> insts_set;
}

let (abs_annotation : (abstraction * expr * expr) Hmap.key) = Hmap.Key.create ()

let abstract abstraction oldpred newpred expr =
  let newexpr = 
          replace_all_opt
           (fun e -> 
             match e with
             | Cons("apply", [p;arg], a) when equiv p oldpred -> 
                 let new_abs_var_name = Printf.sprintf "__abs_var_%s" (print_expr newpred) in
                 Some(Binder(Forall, new_abs_var_name, abstraction.abstract_type, 
                   (fun nvar ->
                     let fsigma = abstraction.fsigma nvar arg in
                     let newapply =  Cons("apply", [newpred;nvar], a) in
                     let combined = mk_imply fsigma newapply in
                     combined),
                   Hmap.(empty |> add abs_annotation (abstraction, newpred, arg))
                 ))
             | _ -> None
           ) expr
           in
  newexpr 
  
let rec movepositive pos e =
      match e with
      | Cons(op, l, a) when op = "and" || op="or" || op = "not" || op = "=>"->
          let rec upgradebinder dealt todo =
            match todo with
            | [] -> Cons(op, dealt, a)
            | (t, same)::q ->
               let npos = if same then pos else not pos in
              (
                match ((movepositive npos t), npos) with
                | (Binder(Forall, n, vt, f, ab), (true as b)) -> Binder((if same then Forall else Exists), n, vt, (fun x -> upgradebinder dealt (((f x), b)::q)), Hmap.rem abs_annotation ab)
                | (Binder(Exists, n, vt, f, ab), (false as b)) -> Binder((if same then Exists else Forall), n, vt, (fun x -> upgradebinder dealt (((f x), b)::q)), Hmap.rem abs_annotation ab)
                | (expr, _) -> upgradebinder (dealt@[expr]) q
              )
          in
          let poslist = match op with
            | "and" | "or" -> List.map (fun x -> true) l
            | "not" -> [false]
            | "=>" -> [false;true]
            | _ -> failwith "poslist called with non known boolean operation"
            in
          let res = upgradebinder []  (List.combine l poslist) in
          res
      | Binder(bt, n, vt, f, a) ->  let ppos = if bt = Forall then pos else not pos in 
                                    Binder(bt, n, vt, (fun expr -> movepositive pos (f expr)), if ppos then Hmap.rem abs_annotation a else a)   
      | _ -> e
  
let eliminate clause =
  let quantifiersmoved = movepositive true clause in
  let rec instantiate ctx expr =
    let a = get_annot expr in
    match (expr, Hmap.find abs_annotation a) with
    | (_,Some(abstraction, newpred, arg)) -> 
        let i = Insts_set.elements (abstraction.insts arg (mk_tuple ctx)) in
        Cons("and", List.map (fun (a,q) -> Cons("=>", [(abstraction.fsigmaq q a arg); Cons("apply", [newpred; a], Hmap.empty)], Hmap.empty)) i, Hmap.empty)
    | (Cons(op, l, a), None) when op = "and" || op="or" || op = "=>" || op = "not"-> 
        let l' = List.fold_left (fun (donel, restl) e -> match restl with | [] -> failwith "impossible" | e::q -> let e' = instantiate (ctx @ donel @ q) e in (donel@[e'], q)) ([], l) l in
        Cons(op, fst l', a)
    | (Binder(b, name, t, f, a), None) -> Binder(b, name, t, (fun e -> instantiate ctx (f e)), a)
    | (Cons(_, _, _), None) -> expr   
  in
  instantiate [] quantifiersmoved
  
    
let dataabs abstraction oldpred newpred expr =
  eliminate (abstract abstraction oldpred newpred expr)
    
    
let eliminate_horn h = transform_clauses eliminate h

let abstract_horn f h =
  let npreds = List.map (fun (pname, ptype) -> 
     let (nname, abstraction) = f pname ptype in
     (nname, abstraction.abstract_type)) (snd h) in
  let (newc, _) = transform_clauses (fun c -> List.fold_left (fun newc (pname, ptype) -> 
                                                let (nname, abstraction) = f pname ptype in
                                                abstract abstraction (mk_const pname) (mk_const nname) newc) c (snd h)) h in
  (newc, npreds)
  
let dataabs_horn f h = 
  let abstracted = abstract_horn f h in
  eliminate_horn abstracted
  
      
   
