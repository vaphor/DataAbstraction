open Hmap

type annotations = Hmap.t


(*List of binders*)
type binder = Forall | Exists

type expr =
  | Binder of binder * string (*suggested name*) * expr (*param type*) *(expr -> expr) * annotations
  | Cons of string * expr list * annotations

(*Empty annotation constructor*)
let no_annot = Hmap.empty
let get_annot e =  
  match e with
  | Cons(_, _, a) -> a
  | Binder(_, _, _, _, a) -> a

let mk_const str = Cons(str, [], no_annot)
let mk_unit = mk_const "()"
let mk_true = mk_const "true"
let mk_false = mk_const "false"
let mk_or l = Cons("or", l, no_annot)
let mk_and l = Cons("and", l, no_annot)
let mk_imply a b = Cons("=>", [a;b], no_annot)
let mk_ite b e1 e2 = Cons("ite", [b;e1;e2], no_annot)
let mk_eq a b = Cons("=", [a;b], no_annot)
let mk_select a i = Cons("select", [a;i], no_annot)
let mk_store a i v= Cons("select", [a;i; v], no_annot)

(*Replaces in top down non recursive all expressions which have a replacement (does not return None) by the new expression.
  This function goes through binders*)
let rec replace_all_opt f e =
  let r = f e in
  match r with
  | Some(e') -> e'
  | None -> 
    (
      match e with
      | Cons(str, args, h) -> Cons(str, List.map (replace_all_opt f) args, h)
      | Binder(bt, name, vtype, fb, annot) -> 
         Binder(bt, name, vtype, (fun expr ->
           replace_all_opt f (fb expr)), annot)
    )
    
let rec unusedname ctx basename =
  let rec nname basename suc v=
     if List.exists (fun e -> e = basename  ^ (suc v)) ctx then
        nname basename  suc (v+1)
     else
        basename  ^ (suc v)
   in
   let suc i = if i = 0 then "" else string_of_int i in
   nname basename suc 0

  
    
(*string associated with binder*)
let binder_as_string b =
  match b with
  | Forall -> "forall"
  | Exists -> "exists"

let binder_from_string str =
  if str = binder_as_string Forall then Forall 
  else if str = binder_as_string Exists then Exists 
  else failwith (Printf.sprintf "String %s is not a binder" str)




  

(*Replaces all binders as Cons with correct naming. 
  Additional names to avoid in binders can be specified using ctx*)
let binders_as_cons ?ctx:(ctx=[]) e =
  let rec get_used_names e =
    match e with
    | Cons(str, args, _) -> str::(List.flatten (List.map get_used_names args))
    | Binder(bt, vn, vt, f, _) -> get_used_names (f (mk_const "_")) @ (get_used_names vt)
  in
    
  let rec trs_binders ctx e =
    match e with
    | Cons(str, l, a) -> Cons(str, List.map (trs_binders ctx) l, a)
    | Binder(bt, name, vtype, fb, annot) -> 
       let newname = unusedname ctx name in
       let newvar = mk_const newname in
       Cons(binder_as_string bt, [newvar; vtype; trs_binders (newname::ctx)  (fb newvar)], annot)
  in
  trs_binders ((get_used_names e) @ ctx) e
  

(*Reads the expression an transforms Cons(Binder, [vn;vt;e], _) into the corresponding Binder*)
let rec binders_from_cons e = 
  match e with
  |Cons(binder as b, [Cons(vname, [], _) as var;vtype;expr], a) when b = binder_as_string Forall || b = binder_as_string Exists ->
    Binder(binder_from_string b, vname, vtype, 
      (fun x -> 
        replace_all_opt (fun v -> if v=var then Some(x) else None) (binders_from_cons expr)
      ), a)
  | Cons(str, l, a) -> Cons(str, List.map binders_from_cons l, a)
  | Binder(op, name, vtype, fb, a) -> Binder(op, name, vtype, (fun x -> binders_from_cons (fb x)), a)

(* Verifies if two expressions are equivalent without caring about annotations and binder names *)
let equiv e1 e2 =
  let (e1, e2) = (binders_from_cons e1, binders_from_cons e2) in
  let rec equivctx ctx e1 e2 =
    match e1, e2 with
    | Cons(binder, [vn1;vt1;e1], _), Cons(binder2, [vn2;vt2;e2], _) when 
        binder = binder2 && (binder = binder_as_string Forall || binder = binder_as_string Exists) ->
        failwith "Should not happen as binders have been constructed"
    | Cons(str1, l1, _), Cons(str2, l2, _) when str1 = str2 && List.length l1 = List.length l2 ->
        List.for_all2 (equivctx ctx) l1 l2
    | Binder(b1, vn1, vt1, f1, _), Binder(b2, vn2, vt2, f2, _) when b1 = b2 && equivctx ctx vt1 vt2 ->
       let str = unusedname ctx vn1 in
       let e = mk_const str in
       equivctx (str::ctx) (f1 e) (f2 e)
    | _ -> false
  in
  equivctx [] e1 e2
  
  
let rec remove_useless_binders e =
  let etmp = binders_as_cons e in
  let rec elim_forall e =
    match e with
    | Cons(str, arg, a) ->
     (
       let argrm = List.map elim_forall arg in
       match (str,argrm) with 
       | (forall, [vn;vt;fe]) when forall = binder_as_string Forall ->
         (
           let rec rmotherforalls expr =
             match expr with
             | Cons(forall, [vn'; vt';f], _) -> rmotherforalls f
             | _ -> expr
             in
           let fe' = rmotherforalls fe in
           let removable =
             match fe' with
             | Cons("=>", [x;y], _) -> 
               (
                 let rec ok x =
                   match x with
                   | Cons("=", [x'; y'], _) when equiv x' vn && not (equiv y' vn)-> Some(y')
                   | Cons("=", [x'; y'], _) when equiv y' vn && not (equiv x' vn)-> Some(x')
                   | Cons("and", l, _) -> let ok' z = match ok z with None -> false | Some(_) -> true in if List.exists ok' l then ok (List.find ok' l) else None
                   | _ -> None
                 in
                 ok x
               )
             | _ -> None in
            match removable with
            | None -> Cons(str, argrm, a)
            | Some(y) -> replace_all_opt (fun x -> if x = vn then Some(y) else None) fe
           )
         | _ -> Cons(str, argrm, a)
       )
      | _ -> failwith "no binders expected here"     
     in
     let eliminated = elim_forall etmp in
     binders_from_cons eliminated
     
     
let simplify_syntactic_eq expr =
  replace_all_opt (fun x -> match x with | Cons("=", [x;y], a) when x=y -> Some(Cons("true", [], a)) | _ -> None) expr

let rec normalize_eq_ordering expr =
  match expr with
  | Cons("=", ([x;y] as l), a) -> Cons("=", List.sort (Pervasives.compare) l, a)
  | Cons(str, l, a) -> Cons(str, List.map normalize_eq_ordering l, a)
  | Binder(op, name, vtype, fb, a) -> Binder(op, name, vtype, (fun x -> normalize_eq_ordering (fb x)), a)
  
let rec rm_duplicates mlist =
  List.fold_left (fun curr x -> if List.exists (fun e -> e = x) curr then curr else curr@[x]) [] mlist
  
let rec simplify_bool expr =
  match expr with
  | Cons(op, l, a) ->
   (
    let l' = List.map simplify_bool l in
    match (op, l') with
    | ("ite", [Cons("true", [], _); a;b]) -> simplify_bool a
    | ("ite", [Cons("false", [], _); a;b]) -> simplify_bool b
    | ("=>", [Cons("true", [], _); e]) -> simplify_bool e
    | ("=>", [e1; Cons("=>", [e2;e3], _)]) -> simplify_bool (Cons("=>", [Cons("and", [e1; e2], Hmap.empty);e3], Hmap.empty))
    | ("and", l') -> 
      let lands = List.flatten (List.map (fun x -> match x with
        | Cons("and", l2, _) -> l2
        | _ -> [x]) l') in
      let lfiltered = List.filter (fun x -> match x with Cons("true", [], _) -> false | _ -> true) lands in
      let final = rm_duplicates lfiltered in
        
      (
      match final with
      | [] -> Cons("true", [], Hmap.empty)
      | [x] -> simplify_bool x
      | _ -> if List.length final  = List.length l' then Cons(op, l', a) else simplify_bool (Cons("and", final, Hmap.empty))
      )
    | _ -> Cons(op, l', a)
   )
  | Binder(bt, n, t, f, a) -> Binder(bt, n, t, (fun e -> simplify_bool (f e)), a)


let rec simplify_arrays expr =
  match expr with
  | Cons(op, l, a) ->
   (
    let l' = List.map simplify_arrays l in
    match (op, l') with
    | ("select", [Cons("store", [a;i;v], _); j]) -> simplify_arrays (mk_ite (mk_eq i j) v (mk_select a j))
    | _ -> Cons(op, l', a)
   )
  | Binder(bt, n, t, f, a) -> Binder(bt, n, t, (fun e -> simplify_arrays (f e)), a)
  
let rec exists_expr f x =
  if f x then true else
  match (binders_as_cons x) with
  | Cons(str, args, _) -> List.exists (exists_expr f) args
  | Binder(b, vn, vt, fb, _) -> failwith "impossible"
  
    
  
        
 
     
let rec print_expr expr =
  let e = binders_as_cons expr in
  match e with
  | Cons( str, [], _) -> Printf.sprintf "%s" str 
  | Cons(str, l, _) -> Printf.sprintf "(%s %s)" str (String.concat " " (List.map print_expr l))
  | _ -> failwith "no binders expected here" 
  
  
let tuple_name_annotation = Hmap.Key.create ()

let mk_tuple l =
  Cons("Tuple", l, no_annot)
  
let mk_named_tuple l =
  Cons("Tuple", List.map fst l, Hmap.(empty |> add tuple_name_annotation (List.map snd l)))

let mk_pair e1 e2 = mk_tuple [e1;e2]
let mk_named_pair (e1, n1) (e2, n2) = mk_named_tuple [(e1,n1); (e2,n2)]
  
let rec extract e n=  Cons("extract", [e;mk_const (string_of_int n)], no_annot)

let efst x = extract x 0
let esnd x = extract x 1

let rec split_tuple_binders e = 
  match e with
  | Cons(str, l, a) -> Cons(str, List.map split_tuple_binders l, a)
  | Binder(bt, v, Cons("Tuple", lt, ap), f, a) ->
      let lname = 
        match Hmap.find tuple_name_annotation ap with
        | None -> List.mapi (fun i _ -> Printf.sprintf "%s_%i" v i) lt
        | Some(al) -> al
      in
      let combined = List.combine lt lname in
      let newe = List.fold_left (fun newf (nt, nname) -> (fun args -> Binder(bt, nname, nt, (fun v -> newf (v::args)), no_annot))) (fun l -> f (mk_tuple l)) (combined) [] in
      split_tuple_binders newe
  | Binder(bt, v, t, f, a) -> Binder(bt, v, t, (fun x -> split_tuple_binders (f x)), a)
  
let rec simplify_tuples e =
  match e with
  | Cons(op, x, a) ->
    (
      let l = List.map simplify_tuples x in
      match (op, l) with
      | ("extract", [Cons("Tuple", l, _); Cons(n, [], _)]) -> 
           List.nth l (int_of_string n)
      | ("Tuple", l) -> 
        (
          match l with
          | [] -> mk_unit
          | Cons("extract", [e;Cons("0", [], _)], _)::q -> 
              let rec ok l start=
                match l with
                | [] -> true
                | Cons("extract", [e';Cons(n, [], _)], _)::q when n = string_of_int start && equiv e' e -> ok q (start+1)
                | _ -> false
              in
              if ok q 1 then e else Cons(op, l, a)
          | _ -> Cons(op, l, a)
        )
      | ("=", [Cons("Tuple", l1, _); Cons("Tuple", l2, _)]) when List.length l1 = List.length l2 -> mk_and (List.map2 (fun e1 e2 -> mk_eq e1 e2) l1 l2)
      | _ -> Cons(op, l, a)
    )
  | Binder(bt, n, t, f, a) -> Binder(bt, n, t, (fun e -> simplify_tuples (f e)), a)
  
  
  
  
let ackermanise e = 
  let etmp = binders_as_cons (simplify_arrays e) in  
  let rec acker e =
    match e with
    | Cons("forall", [vn;Cons("Array", [indt;valt], at);e'], a) -> 
      (
        let e'= acker e' in
        let (ebase, redoforall) = 
          let rec compute e' =
            match e' with
            | Cons("forall", [v;t;expr], a) -> let (ebase, redo) = compute expr in (ebase, fun ebase -> Cons("forall", [v;t;redo ebase], a))
            | _ -> (e', fun e' -> e')
          in
          compute e'
        in
        let rec get_array_reads ebase =
          match ebase with
          | Cons("forall", [v;_;e'], _) | Cons("exists", [v;_;e'], _) ->
            (
               match (get_array_reads e') with 
               | None -> None
               | Some(l) when List.exists (fun x -> exists_expr (fun y -> equiv y v) x) l -> None
               | reads -> reads
            )
          | Cons("select", [a;i], _) when a = vn -> (match get_array_reads i with None -> None | Some(l) -> Some(i::l))
          | Cons(str, args, _) when List.exists  (fun x -> x = vn) args -> None
          | Cons(str, args, _) -> List.fold_left (fun tot r -> match (tot, (get_array_reads r)) with
                                                               | None, _ -> None
                                                               | _, None -> None
                                                               | Some(l1), Some(l2) -> Some(l1 @ l2)) (Some([])) args
          | _ -> failwith (Printf.sprintf "no binders here (get_array_reads). Expr is %s\n" (print_expr ebase))
        in
        let reads = get_array_reads ebase in
        match reads with
        | None -> Cons("forall", [vn;Cons("Array", [indt;valt], at);e'], a)
        | Some(reads) -> 
                        let reads=List.sort_uniq Pervasives.compare reads in
                        let res =(
                        match reads with
                        | [] -> e'
                        | [r] -> Binder(Forall, "acker", valt, (fun v -> replace_all_opt (fun x -> if equiv x (mk_select vn r) then Some(v) else None) e'),no_annot) 
                        | reads ->
                          let final = Binder(Forall, "acker", 
                                mk_named_tuple (List.mapi (fun i _ -> (valt, Printf.sprintf "vacker_%i" i)) reads), 
                                (
                                  fun v -> 
                                    let diff = mk_and (List.flatten (List.mapi (fun i r1 -> 
                                                            (List.mapi (fun j r2 -> 
                                                              let v1 = extract v (i) in
                                                              let v2 = extract v (j) in
                                                              mk_imply (mk_eq r1 r2) (mk_eq v1 v2)
                                                            ) reads)) reads)) in
                                    let replace i r e=replace_all_opt (fun x -> if equiv x (mk_select vn r)  then Some(extract v (i)) else None) e in
                                    let newe = mk_imply diff (snd (List.fold_left (fun (i, e) r -> (i, replace i r e)) (0, ebase) reads)) in
                                    redoforall newe
                                ), no_annot) 
                           in
                           final
                         ) in
                         binders_as_cons res
      )
    | Cons(str, args, a) -> Cons(str, List.map acker args, a)
    | _ -> failwith "no binders expected here"
  in
  binders_from_cons (acker etmp)
  

let rec simplify ?acker:(acker=false) e = 
  let rec simplify_noacker e = 
    let nopairs = simplify_tuples (split_tuple_binders e) in
    let qsimpl = remove_useless_binders nopairs in
    let arraysimp = simplify_arrays qsimpl in
    let simpeq = simplify_syntactic_eq (normalize_eq_ordering arraysimp) in
    let boolsimp = simplify_bool simpeq in
    if equiv boolsimp e then e else simplify_noacker boolsimp
  in
  let simp = simplify_noacker e in
  if acker then 
    let ackered = simplify_tuples (split_tuple_binders (ackermanise simp)) in
    if equiv ackered simp then simp else simplify ~acker:acker ackered
  else simp 
  
  
  
 
