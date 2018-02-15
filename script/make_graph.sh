#!/bin/bash
#TODO: remove redundancy of "-R ~~" with Makefile
coqdep -dumpgraph graph.dot \
    -R coq CRELLVM -R lib/paco/src Paco -R lib/vellvm/src Vellvm -R lib/vellvm/lib/sflib sflib \
    -R lib/vellvm/lib/metalib metalib -R lib/vellvm/lib/cpdtlib Cpdt -R lib/vellvm/lib/compcert-2.4 compcert \
    **
dot -Tpng graph.dot > graph.png
