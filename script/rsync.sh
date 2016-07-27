#!/usr/bin/env bash
PROOF_BUILD_DIR=.proof_build

rsync -av --delete --exclude '*.vo' --exclude '*.vio' --exclude '*.v.d' --exclude '*.glob' --exclude '.*.aux' \
    --exclude 'Makefile.coq' --exclude '_CoqProject' \
    --exclude 'simplberry-tests/' \
    --exclude 'lib/llvm/' --exclude '.build' \
    --exclude 'ocaml/build_/' --exclude '*.ml' --exclude '*.mli' \
    --exclude '.git' \
    --exclude "$PROOF_BUILD_DIR" \
    . "$PROOF_BUILD_DIR"

