#!/usr/bin/env bash
PROOF_BUILD_DIR=.build-proof

rsync -av --copy-links --delete --prune-empty-dirs \
    --exclude "$PROOF_BUILD_DIR" \
    --exclude "lib/llvm/" --exclude "ocaml" \
    --include '*/' \
    --include '*.v' --include 'Makefile' \
    --include '*.ott' --include 'fixextract.py' \
    --exclude '*' \
    './' "$PROOF_BUILD_DIR/"

