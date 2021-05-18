open Dataabs
open Expr

let top= mk_const "___top___"
  
let fsort l =
  match l with
  | [x] -> mk_tuple l
  | [x;y] ->mk_tuple [mk_ite (Cons("<=", [efst x;efst y],Hmap.empty)) x y; mk_ite (Cons("<=", [efst x;efst y],Hmap.empty)) y x]
  | _ -> failwith "using more than 2 cells is not implemented in sort"
(*   Cons("Sort", List.map efst l, Hmap.empty) *)
  
let comp e1 e2 = Cons("<=", [efst e1; efst e2], Hmap.empty)
  
  
let rec get_base_array a =
  match a with
  | Cons("store", [x;ind;v], _) -> 
      let (basea, depth, l) = get_base_array x in
      (basea, depth, (ind, v)::l)
  | Cons("select", [x;ind], _) ->
      let (basea, depth, l) = get_base_array x in
      (basea, depth+1, [])
  | _ -> (a, 0, [])

let relevant a ctx =
  let rec read avar depth expr =
      match expr with 
      | Cons("select", [b;i], _) ->
         let (basea, d, stores) = get_base_array b in
         let recreads = match b with | Cons(_, [], _) -> read avar depth i | _ -> (read avar depth i) @ (read avar depth b) in
         if (equiv basea avar) && (d=depth) then
           i::recreads
         else 
           recreads
      | a when equiv a avar -> [top]
      | Cons(str, args, _) -> List.flatten (List.map (read avar depth) args)
      | Binder(_, _, _, f, _) -> List.map (fun x -> if exists_expr (fun x -> equiv x top) x then top else x) (read avar depth (f top))      
  in
  let (basea, depth, l) = get_base_array a in
  match basea with
  | Cons(str, [], _) -> (read basea depth ctx) @ (List.map fst l)
  | _ -> [top]
  
let mk_cellabs t1 t2=
      {
         name = Printf.sprintf "cell1";
         concrete_type = Cons("Array", [t1;t2], Hmap.empty);
         abstract_type = mk_named_pair (t1, "i") (t2, "v");
         fsigma= (fun iv a -> Cons("=", [esnd iv; (Cons("select", [a; efst iv], Hmap.empty))], Hmap.empty));
         fsigmaq  = (fun q iv a ->  Cons("=", [esnd iv; (Cons("select", [a; efst iv], Hmap.empty))], Hmap.empty));
         insts = (fun a ctx ->
            let r = relevant (simplify a) (simplify ctx) in
            if List.exists (fun x -> equiv x top) r && not (exists_expr (fun x -> equiv x (mk_const "_")) ctx) then Printf.eprintf "Got top in relevant set. Extracted from relevant %s in ctx\n%s\n\n" (print_expr (simplify a)) (print_expr (simplify ctx));
            let rtop = List.filter (fun x -> not (equiv x top)) r in
            let ind = if rtop =[] then [mk_const "17"] else rtop in
            let iset = List.map (fun r -> 
              let aabs = mk_pair r (mk_select a r) in
              let q = mk_unit in
              (aabs, q)
            ) ind in
           Insts_set.of_list iset);
      }
      
let mk_currified_cellabs t1 t2=
        let t = Cons("Array", [t1;t2], Hmap.empty) in
        let rec mabs t=
           match t with
           | Cons("Array", [t1;t2], _) -> 
            (
             let fabs = mk_cellabs t1 t2 in
             match mabs t2 with
             | None -> Some(fabs)
             | Some(sabs) -> Some(Combinators.compose (Combinators.tuple_dot [(Combinators.mk_id t1);sabs]) fabs)
            )
           | _ -> None
         in
         match mabs t with
         | None -> failwith "Impossible"
         | Some(mabs) -> mabs
      
