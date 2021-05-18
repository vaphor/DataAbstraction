open Expr
open Io
open Dataabs
open Combinators
open Cellabs

let rec mk_list n =
  match n with
  | 0 -> []
  | k -> (k-1)::(mk_list (k-1))



type full_abs=string (*pname*) -> expr (*ptype*) -> (string (*abs panme*) * abstraction (*abstraction*))

let abscelln t1 t2 n = duplicate_distinct (mk_cellabs t1 t2) (Cellabs.fsort, Cellabs.comp) n 
let abscurcelln t1 t2 n = duplicate_distinct (mk_currified_cellabs t1 t2) (Cellabs.fsort, Cellabs.comp) n 

(*Here we define our full abstraction!*)
let all_arrays_cell n pname ptype =
   let rec create_abs ptype =
    match ptype with
     | Cons("Tuple", l, a) -> 
         tuple_dot (List.map create_abs l)
     | Cons("Array", [t1;t2], a) -> 
         abscelln t1 t2 n
     | _ -> mk_id ptype 
   in
   (pname^"_abs", create_abs ptype)
   
(*let all_arrays_curr_cell n pname ptype =
   let rec create_abs ptype =
    match ptype with
     | Cons("Tuple", l, a) -> 
         tuple_dot (List.map create_abs l)
     | Cons("Array", [t1;t2], a) -> 
         duplicate (mk_cellabs t1 t2) n
     | _ -> mk_id ptype 
   in
   let rec final cabs =
     let cabscomp =  create_abs (cabs.abstract_type) in
     if cabs.abstract_type = cabscomp.abstract_type then 
       cabs
     else
       final (compose cabscomp cabs)
   in
   (pname^"_abs", final (create_abs ptype))*)
   
   
let all_arrays_curr_cell n pname ptype =
   let rec create_abs ptype =
    match ptype with
     | Cons("Tuple", l, a) -> 
         tuple_dot (List.map create_abs l)
     | Cons("Array", [t1;t2], a) -> 
         abscurcelln t1 t2 n
     | _ -> mk_id ptype 
   in
   (pname^"_abs", create_abs ptype)
  
(*indtype (recpectively valtype) is the index (respectively value) type of the array to abstract*)
let array_smashing indtype valtype =  compose (reorganize_tuples (mk_tuple [indtype;valtype]) (mk_const "1")) (mk_cellabs indtype valtype)

let smash_all pname ptype =
   let rec create_abs ptype =
    match ptype with
     | Cons("Tuple", l, a) -> (*Tuples are abstracted by the tuple abstraction*)
         tuple_dot (List.map create_abs l)
     | Cons("Array", [indtype;valtype], a) -> (*Arrays are abstracted by array smashing*)
         array_smashing indtype valtype
     | _ -> mk_id ptype (*Other types are abstracted by the identity*)
   in
   (pname^"_abs", create_abs ptype) (*We return the name for the abstracted predicate and the abstraction*)

   
   

   
module ExprMap = Map.Make(struct type t = expr let compare = Pervasives.compare end);;

let add_elem t e m =
  let prev_val = if ExprMap.mem t m then ExprMap.find t m else [] in
  ExprMap.add t (e::prev_val) m
   
let array_cell_same_index n pname ptype =
  let non_array_positions= ref [] in
  let array_positions_for_type = ref ExprMap.empty in
  
  let rec create_abs ptype pos=
    match ptype with
     | Cons("Tuple", l, a) ->
         let children = List.mapi (fun i c -> create_abs c (i::pos)) l in
         let nabs= tuple_dot children in
         nabs
     | Cons("Array", [t1;t2], a) -> 
         array_positions_for_type:= add_elem t1 pos !array_positions_for_type;
         non_array_positions:= (List.map (fun i -> (t2, 1::i::pos)) (mk_list n))@ (!non_array_positions);
(*          let nposval i = position^(string_of_int i)^"_"^"1" in *)
(*          let nposind i = (fun e -> efst (extract (get_pos e) i)) in *)
         let nabs = duplicate (mk_cellabs t1 t2) n in
         (*if not (List.exists (fun (t, pos) -> t=t1) !assoc_list) then
             assoc_list:=(t1, (fun e -> List.map (fun i -> nposind i e) (mk_list n)))::(!assoc_list)
         else
         (
           let lindex = snd (List.find (fun (t, pos) -> t=t1) !assoc_list) in
           let conds = (fun (e : expr) -> mk_and (List.mapi (fun i ind -> mk_eq (nposind i e) ind) (lindex e))) in
           conds_list:=conds:: !conds_list
         )
         ;*)
         nabs
          (* let lindex = snd (List.find (fun (t, pos) -> t=t1) !assoc_list) in
           if n =1 then "("^(List.hd lindex)^","^position^"1)"
           else  Printf.sprintf "(%s)" (String.concat "," (List.mapi (fun i pos -> "("^pos^","^(nposval i)^")") lindex)) 
         in*)
(*          (nabs, ntuple)        *)
     | _ -> 
       non_array_positions:= (ptype, pos)::!non_array_positions;
       let nabs = mk_id ptype in
       nabs
   in
   let as_string pos = mk_const (String.concat "_" (List.map string_of_int (List.rev pos))) in
   let cabs=create_abs ptype [] in
   
   let put_celln = ExprMap.map (fun poslist -> List.map (fun pos -> List.map (fun i -> as_string (0::i::pos)) (mk_list n)) poslist) !array_positions_for_type in
   let as_tuples = ExprMap.map (fun poslist -> List.map (fun inds -> mk_tuple inds) poslist) put_celln in
   let final = ExprMap.map (fun poslist -> (List.length poslist, mk_tuple poslist)) as_tuples in
   let narray_pos_tuple =mk_tuple (List.map as_string (List.map snd !non_array_positions)) in
   let tuples = narray_pos_tuple::(List.map (fun (k,(l, t)) -> t) (ExprMap.bindings final)) in
   let reorganize_str =mk_tuple tuples in
   
   let id_non_array = (mk_id (mk_tuple (List.map fst !non_array_positions))) in
   let unionabs (t, (nb, l)) = union (mk_tuple (List.map (fun i -> mk_tuple(List.map (fun i -> t) (mk_list n))) (mk_list nb))) in
   let cunion= tuple_dot (id_non_array::(List.map unionabs (ExprMap.bindings final))) in
   (pname^"_abs", compose cunion (compose (reorganize_tuples cabs.abstract_type reorganize_str) cabs))
   
  (* List.map (fun i -> List.rev(0::i::pos)) (mk_list n)) poslist) in
      
      Printf.sprintf "(%s)" (String.concat "," (List.map (fun pos -> String.concat "_" (List.map string_of_int (List.rev (0::pos)))) poslist))) in
   
   match ptype with
   | Cons("Tuple", _, _) -> 
     let cabs = create_abs ptype (fun e -> e) in
     (pname^"_abs", compose (restrict cabs.abstract_type (fun e -> mk_and (List.map (fun f -> f e) !conds_list))) cabs) 
   | _ -> all_arrays_cell n pname ptype*)
   
    (*We return the name for the abstracted predicate and the abstraction*)
