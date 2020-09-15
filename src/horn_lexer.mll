{
(*This file is part of Vaphor

    Vaphor is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Vaphor is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with Vaphor.  If not, see <https://www.gnu.org/licenses/>. *)
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
| tupleword {let s = Lexing.lexeme lexbuf in WORD(s)}
| comment {let s = Lexing.lexeme lexbuf in COMMENT(String.sub s 1 ((String.length s)-1))}
| "(" {LBRACE}
| ")" {RBRACE}
| word {let s = Lexing.lexeme lexbuf in WORD(s)}
| eof {EOF}

and 
ruleTail acc = parse
  | eof { acc }
  | _* as str { ruleTail (acc ^ str) lexbuf }

