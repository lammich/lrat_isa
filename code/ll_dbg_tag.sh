#!/bin/bash

function error() {
  echo $@
  exit 1
}

[ $# == 1 ] || error "Usage: ll_dbg_tag.sh <ll-file>"

IN=$1
OUT="${IN%.ll}.dbg.ll"

echo "$IN -> $OUT"

sed -re 's/call void @(\w+)_ll_dbg_tag_(\w+)/call void @\1_ll_dbg_fun_\2/' "$IN" > "$OUT"


egrep -o 'define void @\w+_ll_dbg_tag_\w+ *\([^)]*\)' "$IN" \
  | sed -re 's/_ll_dbg_tag_/_ll_dbg_fun_/;s/define/declare/' \
  | tee -a "$OUT"




