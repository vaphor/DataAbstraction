open Expr

type command =
| Comment of string
| Clause of expr

type horn = (command list) * ((string * expr) list) (*predicate declaration*)
  


let transform_clauses f (h : horn) =
  let nc = List.map (fun c -> match c with
                     | Comment(str) -> c
                     | Clause(e) -> Clause(f e)) (fst h) in
  (nc, snd h)
  
let simplify ?acker:(acker=false) h = transform_clauses (Expr.simplify ~acker:acker) h
     
         
