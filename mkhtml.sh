#!/bin/bash

ISABELLE=isabelle

# Assemble browser info

ISABELLE_BROWSER_INFO=$($ISABELLE getenv ISABELLE_BROWSER_INFO | sed -re 's/.*=//')

rm -rf docs
mkdir -p docs

cp -a "$ISABELLE_BROWSER_INFO"/* "docs/"


# pandoc -V pagetitle="LRUP Check LLVM" -s index.md > docs/index.docs

