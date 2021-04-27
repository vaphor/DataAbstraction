open Dataabs
open Expr

let rec getarrayreads a ctxtot =
  let rec getarrayreads visited a ctx =
  if List.exists (fun x -> equiv x a) visited then []
  else
  (
  let rec is_array_store_chain b a =
    match b with
    | x when equiv x a -> true
    | Cons("store", [x;ind;v], _) -> is_array_store_chain x a
    | _ -> false in
  match ctx with
  | Cons("select", [b;i], _) when is_array_store_chain b a -> i::(getarrayreads visited a b) @ (getarrayreads visited a i)
  | Cons("=", [a1;a2], _) when equiv a1 a -> 
                                                let rv = (getarrayreads (a::visited) a2 ctxtot) in 
                                             rv @(getarrayreads visited a a2)
  | Cons("=", [a1;a2], _) when equiv a2 a -> 
                                                let rv = (getarrayreads (a::visited) a1 ctxtot) in
                                             rv @(getarrayreads visited a a1)
  | Cons(_, l, _) -> List.flatten (List.map (getarrayreads visited a) l)
  | Binder(op, n, t, f, _) -> []
  )
  in
  getarrayreads [] a ctxtot
  
  
let mk_cellabs t1 t2=
      {
         name = Printf.sprintf "cell1";
         concrete_type = Cons("Array", [t1;t2], Hmap.empty);
         abstract_type = mk_named_pair (t1, "i") (t2, "v");
         fsigma= (fun iv a -> Cons("=", [esnd iv; (Cons("select", [a; efst iv], Hmap.empty))], Hmap.empty));
         fsigmaq  = (fun q iv a ->  Cons("=", [esnd iv; (Cons("select", [a; efst iv], Hmap.empty))], Hmap.empty));
         insts = (fun a ctx ->
            let rtmp = getarrayreads (simplify_tuples a) (simplify_tuples ctx) in
            let r = if rtmp =[] then [mk_const "17"] else rtmp in
            let iset = List.map (fun r -> 
              let aabs = mk_pair r (mk_select a r) in
              let q = mk_unit in
              (aabs, q)
            ) r in
           Insts_set.of_list iset);
      }
