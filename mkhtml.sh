#!/bin/bash

ISABELLE=isabelle

# Assemble browser info

ISABELLE_BROWSER_INFO=$($ISABELLE getenv ISABELLE_BROWSER_INFO | sed -re 's/.*=//')

rm -rf html
mkdir -p html

cp -a "$ISABELLE_BROWSER_INFO"/* "html/"


# pandoc -V pagetitle="LRUP Check LLVM" -s index.md > html/index.html

