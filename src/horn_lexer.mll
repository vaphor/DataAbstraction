{

open Horn_parser
open Localizing

exception Eof 

}

(*Any basic element of the horn language*)
let word = [^' ''\n'')''('';']*
let tupleword = "|tuple("[^'\n'')''('';']*")|"
let newline = "\n" | "\r" | "\r\n"
let comment = ';'[^'\n''\r']*

rule token = parse
  newline { next_line lexbuf; token lexbuf }
| [' ' '\t'] {token lexbuf}
(* | tupleword {let s = Lexing.lexeme lexbuf in WORD(s)} *)
| comment {let s = Lexing.lexeme lexbuf in COMMENT(String.sub s 1 ((String.length s)-1))}
| "(" {LBRACE}
| ")" {RBRACE}
| "," {COMMA}
| "forall" {BINDER("forall")}
| "exists" {BINDER("exists")}
| "declare-rel" {DECLAREREL}
| "declare-fun" {DECLAREFUN}
| "check-sat" {CHECKSAT}
| "assert" {ASSERT}
| "set-logic" {SETLOGIC}
| word {let s = Lexing.lexeme lexbuf in WORD(s)}
| eof {EOF}

and 
ruleTail acc = parse
  | eof { acc }
  | _* as str { ruleTail (acc ^ str) lexbuf }

