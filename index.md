# Fast and Verified UNSAT Proof Checking

Supplementary Material

The supplementary material contains our formalization, the setup for generating the tool, and a small example cnf and lrat file to try it out.


## Inspecting the Proof
  You can browse the [html version](browser_info/Unsorted/llvm_lrat_checker/index.html) of the theories.
  Note that the presentation in the paper has been simplified for better readability, and typically uses shorter names than the actual formalization.

  Good starting points for browsing:

  * [Main Theory](browser_info/Unsorted/llvm_lrat_checker/LRAT_Checker_Impl.html) contains code generation and [final correctness theorem](browser_info/Unsorted/llvm_lrat_checker/LRAT_Checker_Impl.html#LRAT_Checker_Impl.lrat_checker_correct|fact) at end.

  * [DIMACS Grammar](browser_info/Unsorted/llvm_lrat_checker/CNF_Grammar.html) contains our [grammar](browser_info/Unsorted/llvm_lrat_checker/CNF_Grammar.html#CNF_Grammar.cnf_dimacs|const) for Dimacs CNF, a succinct characterization of it's [language](browser_info/Unsorted/llvm_lrat_checker/CNF_Grammar.html#CNF_Grammar.dimacs_reg_language|fact), and a [proof that it is unambiguous](browser_info/Unsorted/llvm_lrat_checker/CNF_Grammar.html#CNF_Grammar.unamb_dimacs|fact).

  * [Semantics of CNF](browser_info/Unsorted/llvm_lrat_checker/SAT_Basic.html), with our definition of [satisfiability](browser_info/Unsorted/llvm_lrat_checker/SAT_Basic.html#SAT_Basic.sat|const).

  * [Abstract Checker](browser_info/Unsorted/llvm_lrat_checker/Relaxed_Assignment.html#Relaxed_Assignment.checker_state|type) contains the abstract transition relation for the checker, and it's [correctness](browser_info/Unsorted/llvm_lrat_checker/Relaxed_Assignment.html#Relaxed_Assignment.checker_trans_rtrancl_pres_invar|thm)

  * Data Structures (the theories contain the abstract versions and the LLVM implementations)
    * [Literal Encoding](browser_info/Unsorted/llvm_lrat_checker/Unsigned_Literal.html)
    * [Reversible Partial Assignment](browser_info/Unsorted/llvm_lrat_checker/Trailed_Assignment.html)
    * [Clause Database](browser_info/Unsorted/llvm_lrat_checker/ClauseDB.html)

    * Concrete checker states:
      [outside proof (op)](browser_info/Unsorted/llvm_lrat_checker/LRAT_Checker_Impl.html#LRAT_Checker_Impl.checker_state_out_proof|type)
      [build-lemma (bl)](browser_info/Unsorted/llvm_lrat_checker/LRAT_Checker_Impl.html#LRAT_Checker_Impl.checker_state_build_lemma|type)
      [in proof (ip)](browser_info/Unsorted/llvm_lrat_checker/LRAT_Checker_Impl.html#LRAT_Checker_Impl.checker_state_in_proof|type)

## Prerequisites
  For building the tool from the generated LLVM test, you need:

  * Clang compiler (I used version 14.0.0, but everything >10.0 should be fine), and make

  For checking the proofs, or viewing the proofs inside Isabelle, you additionally need:

  * Working installation of [Isabelle/HOL](https://isabelle.in.tum.de) with the [Archive of Formal Proofs](https://www.isa-afp.org) installed
    as described [here](https://www.isa-afp.org/using.shtml). We require version = Isabelle-2023, which, at the time of writing, is the current version.


  To be self-contained, this material comes bundled with a stripped-down 2023 version of [Isabelle-LLVM](https://github.com/lammich/isabelle_llvm/tree/2023). You don't need to download that.

## Building the tool
  In the main directory, run

      cd code
      make lrat_checker

  This will generate the executable lrat_checker

## Using the tool
  Invoke the tool as

    lrat_checker <cnf-file> <lrat-file>

  On successful verification, it will print the line <code>s VERIFIED UNSAT</code> and exit with exit-code 0.
  Otherwise, it will print an error message and exit with a non-zero exit code.

  Check out the example. From the main directory, run:

    ./code/lrat_checker ex/ex1.cnf ex/ex1.lrat


## Inspecting the proof inside Isabelle
  Run

      isabelle jedit -d . -l Isabelle_LLVM thys/LRAT_Checker_Impl.thy

  On the first invocation of this command, a base image with the required libraries is built, which may take several minutes.
  When invoked, the IDE will display the last theory of the formal development, where the exported code is generated, and the final correctness theorem is proved.
  Moreover, the IDE will start to verify all dependent theories. If verification is finished (may take another few minutes),
  you can use the navigation features of the IDE to navigate the formalization and inspect the proof state.


## Checking the Proofs and Regenerating the LLVM code
  In the main directory, run

      isabelle build -D .

  This will invoke Isabelle to check all proofs and re-generate the exported code, which is written to <code>code/lrat_checker_export.ll</code> This may take a while, in particular on the first invocation, when Isabelle builds some prerequisites.



