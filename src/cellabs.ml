open Dataabs
open Expr

let top= mk_const "___top___"

let rec get_array_store_chain a =
  match a with
  | Cons("store", [x;ind;v], _) -> 
      let (basea, l) = get_array_store_chain x in
      (basea, (ind, v)::l)
  | _ -> (a, [])

let relevant a ctx =
  let rec read avar expr =
    match expr with 
    | Cons("select", [b;i], _) when equiv (fst (get_array_store_chain b)) avar -> 
      i::(List.flatten (List.map (fun (j, v) -> (read avar j) @ (read avar v)) (snd (get_array_store_chain b))))
    | a when equiv a avar -> [top]
    | Cons(str, args, _) -> List.flatten (List.map (read avar) args)
    | Binder(_, _, _, f, _) -> List.map (fun x -> if exists_expr (fun x -> equiv x top) x then top else x) (read avar (f top))
  in
  let (basea, l) = get_array_store_chain a in
  match basea with
  | Cons(_, [], _) -> read basea ctx
  | _ -> [top]
  
  
let mk_cellabs t1 t2=
      {
         name = Printf.sprintf "cell1";
         concrete_type = Cons("Array", [t1;t2], Hmap.empty);
         abstract_type = mk_named_pair (t1, "i") (t2, "v");
         fsigma= (fun iv a -> Cons("=", [esnd iv; (Cons("select", [a; efst iv], Hmap.empty))], Hmap.empty));
         fsigmaq  = (fun q iv a ->  Cons("=", [esnd iv; (Cons("select", [a; efst iv], Hmap.empty))], Hmap.empty));
         insts = (fun a ctx ->
            let r = relevant (simplify_tuples a) (simplify_tuples ctx) in
            let rtop = List.filter (fun x -> not (equiv x top)) r in
            let ind = if rtop =[] then [mk_const "17"] else rtop in
            let iset = List.map (fun r -> 
              let aabs = mk_pair r (mk_select a r) in
              let q = mk_unit in
              (aabs, q)
            ) ind in
           Insts_set.of_list iset);
      }
