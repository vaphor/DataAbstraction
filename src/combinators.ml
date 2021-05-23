open Expr
open Dataabs
open Io

let mk_id t = 
  {
    name = Printf.sprintf "id";
    concrete_type = t;
    abstract_type = t;
    fsigmaq = (fun q abstract conc -> Cons("=", [abstract; conc], Hmap.empty));
    fsigma = (fun abstract conc -> Cons("=", [abstract; conc], Hmap.empty));
    insts = fun a ctx -> Insts_set.singleton (a, mk_unit);
  }

let flatten_insts iI =List.fold_left (fun l (a, q) -> a::q::l) [] iI


let set_product_map f s1 s2 = 
  Insts_set.fold (fun e1 tot -> Insts_set.fold (fun e2 t -> Insts_set.add (f (e1, e2)) t) s2 tot) s1 Insts_set.empty
  
                   
let rm_duplicates l =
  List.fold_left (fun l e -> if List.exists (fun x -> e=x) l then l else e::l) [] l
                   
                   
let dot ?lefttoright:(b=true) abs1 abs2 =
  
  let fsq q a b = 
      Cons("and", 
        [
          (abs1.fsigmaq (efst q) (efst a) (efst b));
          (abs2.fsigmaq (esnd q) (esnd a) (esnd b))
        ], Hmap.empty) in
  let fs a b = 
      Cons("and", 
        [
          (abs1.fsigma (efst a) (efst b));
          (abs2.fsigma (esnd a) (esnd b))
        ], Hmap.empty) in
  let instset a ctx =
    let (i1, i2) = if b then
    (
      let i1 = abs1.insts (efst a) (mk_pair ctx (esnd a)) in
      let i2 = abs2.insts  (esnd a)  (mk_tuple (ctx::(efst a)::(flatten_insts (Insts_set.elements i1)))) in
      (i1, i2)
      
      
    )
    else
    (
      let i2 = abs2.insts (esnd a) (mk_pair ctx (efst a)) in
      let i1 = abs1.insts  (efst a)  (mk_tuple (ctx::(esnd a)::(flatten_insts (Insts_set.elements i2)))) in
      (i1, i2)
    ) in
    
    let res = set_product_map (fun ((a1, q1),(a2, q2)) -> (mk_pair a1 a2, mk_pair q1 q2)) i1 i2 in
    res
    in      
  {
    name = Printf.sprintf "%s.%s" abs1.name abs2.name;
    concrete_type = mk_pair abs1.concrete_type abs2.concrete_type;
    abstract_type = mk_named_pair (abs1.abstract_type, Printf.sprintf "%s" abs1.name) (abs2.abstract_type, Printf.sprintf "%s" abs2.name);
    fsigmaq = fsq;
    fsigma = fs;
    insts = instset;     
  }

let tuple_dot l = 
  let fsq q a b = mk_and (List.mapi (fun i x -> (x.fsigmaq (extract q i) (extract a i) (extract b i))) l) in
  let fs a b = mk_and (List.mapi (fun i x -> (x.fsigma (extract a i) (extract b i))) l) in
  let instset a ctx =
      let alli = snd (List.fold_left (fun (i, alli) x -> 
                                      let others = List.flatten (List.mapi (fun j _ -> if j=i then [] else [extract a j]) l) in
                                      let instantiated = (Insts_set.elements (List.fold_left Insts_set.union Insts_set.empty alli)) in
                                      let ix =  x.insts (extract a i) (mk_tuple (ctx::(flatten_insts instantiated) @ others)) in
                                     (i+1, alli @ [ix])) (0, []) l) in
      let alliaslist = List.map Insts_set.elements alli in
      let allproduct = List.fold_left (fun res i ->
              List.flatten (List.map (fun r -> List.map (fun x -> r @[x]) i) res)) [[]] alliaslist in
      let restuples = List.map (fun l -> (mk_tuple (List.map fst l),mk_tuple (List.map snd l))) allproduct in
      Insts_set.of_list restuples
    in      
  {
    name = Printf.sprintf "%s" (String.concat "." (List.map (fun x -> x.name) l));
    concrete_type = mk_tuple (List.map (fun x ->  x.concrete_type) l);
    abstract_type = mk_named_tuple (List.map (fun x ->  (x.abstract_type, x.name)) l);
    fsigmaq = fsq;
    fsigma = fs;
    insts = instset;     
  }

(*abs1 \circ abs2 *)
let compose abs1 abs2 =
  if not (equiv (simplify abs2.abstract_type) (simplify abs1.concrete_type)) then
    failwith (Printf.sprintf "Unmatching types in abstraction composition. Abstraction2 abstract type is \"%s\" and abstraction1 concrete type is \"%s\"" 
                              (print_expr (simplify abs2.abstract_type)) (print_expr (simplify abs1.concrete_type)))
  ;
  
  let fs a b= 
      Binder(Exists, "__compose_tmp", abs2.abstract_type, (fun new_var ->  Cons("and", 
                                    [abs2.fsigma new_var b; abs1.fsigma a new_var], Hmap.empty)), Hmap.empty)
  in
  let fsq q a b= 
     Cons("and", [abs2.fsigmaq (extract q 1)  (extract q 0) b; abs1.fsigmaq (extract q 2) a (extract q 0)], Hmap.empty)
  in
  
  let instset a ctx =
(*       Printf.eprintf "Composed called with a=%s ctx=\n%s\n\n" (print_expr a) (print_expr (simplify ctx)); *)
      let i2 = Insts_set.elements (abs2.insts a ctx) in
      let i2mx x = List.filter (fun y -> y=x) i2 in
      let fs2 x = abs2.fsigmaq (snd x) (fst x) a in
      let iF =
        List.fold_left
          (fun iF x ->
            let ix = Insts_set.elements (abs1.insts (fst x) (mk_tuple ((fs2 x)::ctx::(flatten_insts ((i2mx x)@iF))))) in
            let iordered = List.map (fun (a1,q1) -> (a1, mk_tuple [fst x; snd x; q1])) ix in
            iF @ iordered
          ) [] i2 in
      Insts_set.of_list iF  
    in
    
  
  {
    name = Printf.sprintf "%so%s" abs2.name abs1.name;
    concrete_type = abs2.concrete_type;
    abstract_type = abs1.abstract_type;
    fsigma = fs;
    fsigmaq = fsq;
    insts = instset;
  }
  

let rec mk_list n =
  match n with
  | 0 -> []
  | k -> (k-1)::(mk_list (k-1))
  
  
let set_to_n_map f n s  = 
  let mkf i ((a1, q1),(a2, q2)) = 
    let e =(a1, q1) in
    let rest = List.map (fun i -> (extract a2 i, extract q2 i))  (mk_list i) in
    f (e::rest) 
  in
  
  snd (List.fold_left 
     (fun (i,stot) _ -> (i-1, set_product_map (mkf i) s stot)) 
     (n-1,s) 
     (mk_list (n - 1))) 
     
let list_product l1 l2 =
  List.flatten (List.map (fun e1 -> List.map (fun e2 -> e1 @ [e2]) l2) l1)

(*let list_to_n_distinct l n =
  List.fold_left (fun res _ -> List.map (fun (sl, m) -> res *)
  
let power n l =
  List.fold_left (fun res _ -> list_product res l) [[]] (mk_list n)
  
let rec combinations n l =
    if n <= 0 then [[]]
    else match l with
         | [] -> []
         | h :: tl ->
            let with_h = List.map (fun l -> l @[h]) (combinations (n - 1) tl) in
            let without_h = combinations n tl in
            with_h @ without_h
  
let duplicate abstraction n =
(*   if n = 1 then abstraction else *)
(*  let is_sorted a =
    List.flatten (List.map (fun i -> List.map (fun j -> Cons("<", [(extract (efst a j); (extract a i)], Hmap.empty)) (mk_list i)) (mk_list n))*)
(*   in *)
  let fsq q a b = 
      Cons("and", 
          (List.map (fun i -> 
          (abstraction.fsigmaq (extract q i) (extract a i) b)) (mk_list n))
        , Hmap.empty) in
  let fs a b = 
      Cons("and", 
          (List.map (fun i -> 
          (abstraction.fsigma (extract a i) b)) (mk_list n))
        , Hmap.empty) in
  let instset a ctx =
    let i = abstraction.insts a ctx in
    let ilist= Insts_set.elements i in 
    let reslist = power n ilist in                              
                                     
    let restuples = List.map (fun l -> (mk_tuple (List.map fst l),mk_tuple (List.map snd l))) reslist in
    Insts_set.of_list restuples
    in      
  {
    name = Printf.sprintf "%sx%i" abstraction.name n;
    concrete_type = abstraction.concrete_type;
    abstract_type = mk_named_tuple (List.map (fun _ ->  (abstraction.abstract_type, Printf.sprintf "%s" abstraction.name)) (mk_list n));
    fsigmaq = fsq;
    fsigma = fs;
    insts = instset;     
  }
  
  
  
  
  
 let duplicate_distinct abstraction (fsort, comp) n =
(*   if n = 1 then abstraction else *)
  let is_sorted a =
    List.flatten (List.map (fun i -> List.map (fun j -> comp (extract a j) (extract a i)) (mk_list i)) (mk_list n))
  in
  let fsq q a b = 
      Cons("and", 
          (List.map (fun i -> 
          (abstraction.fsigmaq (extract q i) (extract a i) b)) (mk_list n)) @ (is_sorted a)
        , Hmap.empty) in
  let fs a b = 
      Cons("and", 
          (List.map (fun i -> 
          (abstraction.fsigma (extract a i) b)) (mk_list n)) @ (is_sorted a)
        , Hmap.empty) in
  let instset a ctx =
    let i = abstraction.insts a ctx in
    let ilist= Insts_set.elements i in
    let reslist = if List.length ilist < n then power n ilist else combinations n ilist in                              
                                     
    let restuples = List.map (fun l -> ((fsort (List.map fst l)),mk_tuple (List.map snd l))) reslist in
    Insts_set.of_list restuples
    in      
  {
    name = Printf.sprintf "%sx%i" abstraction.name n;
    concrete_type = abstraction.concrete_type;
    abstract_type = mk_named_tuple (List.map (fun _ ->  (abstraction.abstract_type, Printf.sprintf "%s" abstraction.name)) (mk_list n));
    fsigmaq = fsq;
    fsigma = fs;
    insts = instset;     
  } 
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  let reorganize_tuples initialtype tree=
(*     Printf.eprintf "Reorganizing tuples typed with %s by %s" (print_expr initialtype) (print_expr tree); *)
(*     let tree = parse_expr str in *)
(*     Printf.printf "Parsed is %s" (print_expr tree); *)
    let rec get_val str t=
      try 
        let fst_elem_index = String.index str '_'  in
        let i = int_of_string (String.sub str 0 fst_elem_index) in
        let rest = String.sub str (fst_elem_index+1) ((String.length str) -(fst_elem_index+1)) in
        get_val rest (extract t i)
      with
      | Not_found -> extract t (int_of_string str)
    in
    
    let rec compute_abs_type tree=
      match tree with
      |  Cons("Tuple", l, _) ->  mk_tuple (List.map compute_abs_type l)
      |  Cons(str, [], _) -> get_val str initialtype
      | _ -> failwith (Printf.sprintf "Unknown value %s for reorganizing tuples" (print_expr tree))
    in
    
    let rec fs a b tree= 
      match tree with
      |  Cons("Tuple", l, _) ->  mk_and (List.mapi (fun i e -> fs (extract a i) b e) l)
      |  Cons(str, [], _) -> mk_eq a (get_val str b)
      | _ -> failwith (Printf.sprintf "Unknwn value %s for reorganizing tuples" (print_expr tree))
    in
    
    let rec fsq q a b tree= 
      match tree with
      |  Cons("Tuple", l, _) ->  mk_and (List.mapi (fun i e -> fsq q (extract a i) b e) l)
      |  Cons(str, [], _) -> mk_eq a (get_val str b)
      | _ -> failwith (Printf.sprintf "Unknown value %s for reorganizing tuples" (print_expr tree))
    in
    
    let rec instset a ctx tree=
      match tree with
      |  Cons("Tuple", l, _) ->  mk_tuple (List.mapi (fun i e -> instset a ctx e) l)
      |  Cons(str, [], _) -> get_val str a
      | _ -> failwith (Printf.sprintf "Unknown value %s for reorganizing tuples" (print_expr tree))
    in     
(*     Printf.eprintf "\n\nabstype is %s\n\n" (print_expr (simplify (compute_abs_type tree))); *)
    {
    name = Printf.sprintf "tuple_reorganisation";
    concrete_type = initialtype;
    abstract_type = compute_abs_type tree;
    fsigma = (fun a b -> fs a b tree);
    fsigmaq = (fun q a b -> fsq q a b tree);
    insts = (fun a ctx -> Insts_set.singleton ((instset a ctx tree, mk_unit)));
   }
   
   
let restrict initialtype cond=
   {
    name = Printf.sprintf "restrict";
    concrete_type = initialtype;
    abstract_type = initialtype;
    fsigma = (fun a b -> mk_and [mk_eq a b; cond b]);
    fsigmaq = (fun q a b -> mk_and [mk_eq a b; cond b]);
    insts = (fun a ctx -> Insts_set.singleton (a, mk_unit));
   }
   
   
let union initialtype =
  let (t, n) =
    match initialtype with
    | Cons("Tuple", a::q, _) -> if List.exists (fun t -> not (equiv t a)) q then failwith "Different types in union, aborting";
                                (a, List.length (a::q))
    | _ -> failwith "union of non tuple type..."
  in
   {
    name = Printf.sprintf "union";
    concrete_type = initialtype;
    abstract_type = t;
    fsigma = (fun a b -> mk_or (List.map (fun i -> mk_eq a (extract b i)) (mk_list n)));
    fsigmaq = (fun q a b -> mk_or (List.map (fun i -> mk_eq a (extract b i)) (mk_list n)));
    insts = (fun a ctx -> Insts_set.of_list (List.map (fun i ->  ((extract a i), mk_unit)) (mk_list n)));
   }
