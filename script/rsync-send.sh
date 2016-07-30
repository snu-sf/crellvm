#!/usr/bin/env bash
PROOF_BUILD_DIR=.proof_build

rsync -av --delete --prune-empty-dirs \
    --exclude "$PROOF_BUILD_DIR" \
    --exclude "lib-llvm/" --exclude "ocaml" \
    --include '*/' \
    --include '*.v' --include 'Makefile' \
    --include '*.ott' --include 'fixextract.py' \
    --exclude '*' \
    './' "$PROOF_BUILD_DIR/"

