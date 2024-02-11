# Executable Checker

This directory contains the LLVM code of the checker exported from Isabelle/HOL and a C++ command line wrapper to produce a usable tool.

* lrat_isa_export.{ll,h}: code exported from Isabelle/HOL
* lib_isabelle_llvm.{c,cpp}: Isabelle/LLVM support library
* main.cpp: Command line wrapper for checker tool

There is also a debug version of the checker, that prints more information in case that checking fails.

## Building
  Building the checker requires
  * Clang compiler (I used version 14.0.0, but everything >10.0 should be fine), and make
  * Boost C++ Libraries with iostreams library

  In this directory, execute

    make

  This will generate the executables `lrat_isa` and `lrat_isa_dbg`.

