# This file is part of Vaphor
# 
#     Vaphor is free software: you can redistribute it and/or modify
#     it under the terms of the GNU General Public License as published by
#     the Free Software Foundation, either version 3 of the License, or
#     (at your option) any later version.
# 
#     Vaphor is distributed in the hope that it will be useful,
#     but WITHOUT ANY WARRANTY; without even the implied warranty of
#     MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#     GNU General Public License for more details.
# 
#     You should have received a copy of the GNU General Public License
#     along with Vaphor.  If not, see <https://www.gnu.org/licenses/>.

OCAMLPREFIX=
OCAMLC=         $(OCAMLPREFIX)ocamlcp -P a
OCAMLOPT=       $(OCAMLPREFIX)ocamloptp.opt -P a
OCAMLYACC=      $(OCAMLPREFIX)ocamlyacc -v
OCAMLLEX=       $(OCAMLPREFIX)ocamllex
OCAMLDEP=       $(OCAMLPREFIX)ocamldep
OCAMLINCLUDES=
OCAMLFLAGS=     -warn-error a -g $(OCAMLINCLUDES)
OCAMLC=         $(OCAMLPREFIX)ocamlc
OCAMLOPT=       $(OCAMLPREFIX)ocamlopt
%.ml: %.mll
	$(OCAMLLEX) $*.mll
%.ml %.mli: %.mly
	$(OCAMLYACC) $*.mly
%.cmo: %.ml %.cmi
	$(OCAMLC) $(OCAMLFLAGS) -c $*.ml
%.cmx: %.ml %.cmi
	$(OCAMLOPT) $(OCAMLFLAGS) -c $*.ml
%.cmi: %.mli
	$(OCAMLC) $(OCAMLFLAGS) -c $*.mli
%.cmo: %.ml
	$(OCAMLC) $(OCAMLFLAGS) -c $*.ml
%.cmx: %.ml
	$(OCAMLOPT) $(OCAMLFLAGS) -c $*.ml
	
all: dataabs
AUTOGEN_ML=	horn_parser.ml  horn_lexer.ml
AUTOGEN_MLI=    horn_parser.mli
AUTOGEN= $(AUTOGEN_ML) $(AUTOGEN_MLI)
ML_FILES=	localizing.ml \
                expressions.ml \
                config.ml \
                $(AUTOGEN_ML) \
                main.ml
                
CMO_FILES=	$(ML_FILES:%.ml=%.cmo)
CMX_FILES=      $(ML_FILES:%.ml=%.cmx)
dataabs: $(CMX_FILES) $(AUTOGEN)
	ocamlopt $(CMX_FILES) -o dataabs

depend: $(AUTOGEN_ML) $(ML_FILES)
	ocamldep $(OCAMLINCLUDES) *.mli *.ml */*.mli */*.ml > depend
clean: 
	rm -f *.cmo *.cmi *.cmx */*.cmi */*.cmo */*.cmx *.output dataabs && \
	rm -f *.o $(AUTOGEN_ML) $(AUTOGEN_MLI) abstract depend *~
include depend
