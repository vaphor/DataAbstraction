open Expr
open Io
open Dataabs
open Combinators
open Cellabs
type full_abs=string (*pname*) -> expr (*ptype*) -> (string (*abs panme*) * abstraction (*abstraction*))


(*Here we define our full abstraction!*)
let all_arrays_cell n pname ptype =
   let rec create_abs ptype =
    match ptype with
     | Cons("Tuple", l, a) -> 
         tuple_dot (List.map create_abs l)
     | Cons("Array", [t1;t2], a) -> 
         duplicate (mk_cellabs t1 t2) n
     | _ -> mk_id ptype 
   in
   (pname^"_abs", create_abs ptype)
   
(*Abstracts an expression of type pair(t1, t2) into t2.
  Equivalent to forget.id of the paper.
  sigma_{forget_first}(e1,e2) = \{e2\} *)
let forget_first t1 t2 =                                                                                                                                                                                              
  {                                                                                                                                                                                                        
    name = Printf.sprintf "forgetfst";                                                                                                                                                                            
    concrete_type = mk_tuple [t1;t2];                                                                                                                                                                                     
    abstract_type = t2;  
    fsigma = (fun abstract conc -> Cons("=", [abstract; (esnd conc)], Hmap.empty));   
    (*fsigmaq is not defined automatically from fsigma, this may happend in the near future*)
    fsigmaq = (fun q abstract conc -> Cons("=", [abstract; (esnd conc)], Hmap.empty));  
    (*The instantiation is finite, we thus use [e2] as instantiation set and it is strongly complete*)
    insts = fun a ctx -> Insts_set.singleton (esnd a, mk_unit);                                                                                                                                                 
  }  
  
(*indtype (recpectively valtype) is the index (respectively value) type of the array to abstract*)
let array_smashing indtype valtype =  compose (forget_first indtype valtype) (mk_cellabs indtype valtype)

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
