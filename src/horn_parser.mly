
%{
open Expr
open Horn
%}

%token LBRACE RBRACE CHECKSAT DECLAREFUN DECLAREREL ASSERT EOF SETLOGIC COMMA
%token <string> WORD COMMENT BINDER

%start horn expr
%type <Horn.horn> horn
%type <Expr.expr> expr
%%


horn:
| LBRACE ASSERT expr RBRACE horn                                      {let command = Clause($3) in (command::(fst $5), snd $5)}
| COMMENT horn                                                        {let command = Comment($1) in (command::(fst $2), snd $2)}
| LBRACE DECLAREREL WORD exprlist RBRACE horn                         {let predname = $3 in
                                                                       let predtype = match $4 with
                                                                         | [] -> failwith "Predicate declaration with empty type"
                                                                         | [a] -> a
                                                                         | l -> mk_tuple l in
                                                                        (fst $6, (predname, predtype)::snd $6)}
| LBRACE DECLAREFUN WORD exprlist expr RBRACE horn                    {let predname = $3 in
                                                                       let predtype = match $4 with
                                                                         | [] -> failwith "Predicate declaration with empty type"
                                                                         | [a] -> a
                                                                         | l -> mk_tuple l in
                                                                       if $5 <> Cons("Bool", [], Hmap.empty) then 
                                                                         failwith "Non boolean function declaration. The tool only handles predicates for the moment";
                                                                        (fst $7, (predname, predtype)::snd $7)}
| LBRACE CHECKSAT RBRACE                                              {([], [])}
| LBRACE SETLOGIC WORD RBRACE horn                                    {$5}


exprlist:
| LBRACE expritems RBRACE {$2}

expritems:
| {[]}
| expr expritems {$1::$2}

commaseparateditems:
| expr {[$1]}
| expr COMMA commaseparateditems {$1::$3}

expr:
| WORD {Cons($1, [], Hmap.empty)}
| LBRACE BINDER vardecllist expr RBRACE {binders_from_cons (List.fold_left (fun e (v, t) -> Cons($2, [Cons(v, [], Hmap.empty);t;e], Hmap.empty)) $4 (List.rev $3))}
| LBRACE BINDER expr expr expr RBRACE {binders_from_cons (Cons($2, [$3; $4; $5], Hmap.empty))}
| LBRACE WORD expritems RBRACE {Cons($2, $3, Hmap.empty)}
| LBRACE commaseparateditems RBRACE {mk_tuple $2}

vardecllist:
| LBRACE vardeclitems RBRACE {$2}

vardeclitems:
| {[]}
| LBRACE WORD expr RBRACE vardeclitems {($2, $3)::$5}


