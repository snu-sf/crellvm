#!/usr/bin/env bash

cp coq/validator.ml coq/validator.ml.backup
while read line; do n=$((++n)) &&  echo $line|sed -e 's/false/failwith \"!'$(($n))\"'/' ; done <coq/validator.ml.backup >coq/validator.ml
