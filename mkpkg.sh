#!/bin/bash

./mkhtml.sh

# Build release tgz package for gratgen
FILES="code/*   thys/*.thy thys/ROOT isabelle-llvm   html  README  ROOTS    ex"

tar -czf lrupchk_llvm.tgz --transform='s|^|lrupchk_llvm/|' $FILES
