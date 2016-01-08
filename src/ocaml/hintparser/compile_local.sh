#!/bin/bash
atdgen -t hintParser.atd
atdgen -j hintParser.atd

ocamlfind ocamlc -c hintParser_t.mli -package atdgen
ocamlfind ocamlc -c hintParser_j.mli -package atdgen
ocamlfind ocamlopt -c hintParser_t.ml -package atdgen
ocamlfind ocamlopt -c hintParser_j.ml -package atdgen
#ocamlfind ocamlopt -c readhintParser.ml -package atdgen

#ocamlfind ocamlopt -o readhintParser \
#  hintParser_t.mli hintParser_t.ml hintParser_j.mli hintParser_j.ml \
#  readhint.ml -package atdgen -linkpkg
