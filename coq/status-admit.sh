#!/usr/bin/env bash

grep -E "(admit|Admitted|TODO)" coq/*/*.v
grep -E "(admit|Admitted|TODO)" coq/*/*.v | wc
