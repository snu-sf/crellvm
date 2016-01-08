#!/bin/bash
atdgen -t hintParser.atd
atdgen -j hintParser.atd

#ocamlfind ocamlc -c hintParser_t.mli -package atdgen
#ocamlfind ocamlc -c hintParser_j.mli -package atdgen
#ocamlfind ocamlopt -c hintParser_t.ml -package atdgen
#ocamlfind ocamlopt -c hintParser_j.ml -package atdgen
