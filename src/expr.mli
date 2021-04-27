open Hmap

(*------------------BASIC TYPE INFORMATIONS----------------*)

(*Type used to annotate expressions*)
type annotations = Hmap.t

(*List of binders*)
type binder = Forall | Exists

type expr =
  | Binder of binder * string (*suggested name*) * expr (*param type*) *(expr -> expr) * annotations
  | Cons of string * expr list * annotations
  
(*------------------Trivial functions to code fast----------------*)

(*Empty annotation constructor*)
val no_annot : annotations
val get_annot : expr -> annotations

(*Creates an expression from a string, that is Cons(str, [], no_annot]*)
val mk_const : string -> expr
val mk_unit : expr

(*------------------Basic operations on Expressions----------------*)

(*Replaces in top down non recursive all expressions which have a replacement (does not return None) by the new expression.
  This function goes through binders*)
val replace_all_opt : (expr -> expr option) -> expr -> expr

(* Verifies if two expressions are equivalent without caring about annotations and binder names *)
val equiv : expr -> expr -> bool

(*------------------Handling binders----------------*)

(*string associated with binder*)
val binder_as_string : binder -> string
val binder_from_string : string -> binder

(*Replaces all binders as Cons with correct naming. 
  Additional names to avoid in binders can be specified using ctx*)
val binders_as_cons : ?ctx:(string list) -> expr -> expr

(*Reads the expression an transforms Cons(Binder, [vn;vt;e], _) into the corresponding Binder*)
val binders_from_cons : expr -> expr

(*Attempts to remove binders which are not relevant :
  for example, things of the form forall b, b = e => x
  can be replaced by x[b <-e] *)
val remove_useless_binders : expr -> expr

(*------------------Boolean Theory----------------*)

val mk_true : expr
val mk_false : expr
val mk_imply : expr -> expr -> expr
val mk_and : expr list -> expr
val mk_or : expr list -> expr
val mk_ite : expr -> expr -> expr -> expr

(*Simplify bool theory*)
val simplify_bool : expr -> expr

(*------------------Equality Theory----------------*)

val mk_eq : expr -> expr -> expr

(*Replaces equalities of the form a=a into true*)
val simplify_syntactic_eq : expr -> expr

(*------------------Array Theory----------------*)

val mk_select : expr -> expr -> expr
val mk_store : expr -> expr -> expr -> expr

(*For now, only applies read over write axioms. Later, might simplify equalities.*)
val simplify_arrays : expr -> expr

(*Is not within simplification as it may generate a non linear number of constraint*)
val ackermanise : expr -> expr


(*-----------------Tuple theory-----------------*)

(*Numbering starts at 0*)
val tuple_name_annotation : (string list) Hmap.key

val mk_pair : expr -> expr -> expr
val mk_named_pair : (expr * string) -> (expr * string) -> expr
val mk_tuple : expr list -> expr
val mk_named_tuple : (expr*string) list -> expr
val efst : expr -> expr
val esnd : expr -> expr
val extract : expr -> int -> expr
val split_tuple_binders : expr -> expr
val simplify_tuples : expr -> expr


(*-----------------Full simplifier-----------------*)

(*Does not ackermanise as ackermanisation is not always worth it*)
val simplify : ?acker:bool -> expr -> expr
(*------------------Printers----------------*)

(*Retrieve string linked to expression in internal format but with binders 
  given names*)
val print_expr : expr -> string









