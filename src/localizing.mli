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

(* A locus is a location in the source text. *)
type locus =
    { locus_file_name:   string;
      locus_file_line:   int;
      locus_file_column: int;
      locus_file_char:   int; }

(* An extent is a pair of loci, giving the beginning and the end of *)
(* a syntactic element (instruction, expression, block, etc). *)
type extent =
    { extent_beg:       locus;
      extent_end:       locus;
      extent_unique_id: int }

(* Set this reference to control the name of the file *)
val current_file_name: string ref

(* Lexer support. *)
val next_line: Lexing.lexbuf -> unit
val extent: Lexing.lexbuf -> extent

(* Parser support. *)
val extopt: extent option -> extent -> extent
val fromto: 'a * extent -> 'b * extent -> extent
val fromtoopt: 'a * extent -> 'b*extent -> 'c*(extent option) -> extent
val extent_unknown: unit -> extent

(* Display of extents. *)
val locus_to_string: locus -> string
val extent_to_string: extent -> string
