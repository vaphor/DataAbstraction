
%{
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
open Expressions

type symbol = string
type info = Info.info
type tree = (info, (symbol * info)) Tree.tree
(*Everything is an expression at this point. We will reinterpret types, foralls, asserts, ... later on*)
%}

%token LBRACE RBRACE EOF
%token <string> WORD COMMENT

%start horn
%type <(Expressions.Info.info, (string * Expressions.Info.info)) Expressions.Tree.tree> horn
%type <(Expressions.Info.info, (string * Expressions.Info.info)) Expressions.Tree.tree> commands
%%

expression_list:
| {[]}
| expression expression_list {$1::$2}

expression:
| WORD {Tree.Leaf($1, Info.none)}
/*| WORD {Interpreted($1)}*/
| LBRACE expression_list RBRACE {Tree.Node($2, Info.none)}

commands:
| EOF {Tree.Leaf("Skip", Info.none)}
| COMMENT commands {$2} 
| expression commands {Tree.Node([Tree.Leaf("SEQ", Info.none); $1; $2], Info.none)}

horn:
| commands {$1}


