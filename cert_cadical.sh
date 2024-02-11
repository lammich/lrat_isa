#!/bin/bash

set -e

SOLVER="cadical -q --lrat"
CHECKER="lrat_isa"

tmpdir=""
fifo=""


function exit_cleanup() {
  if [[ -d "$tmpdir" ]]; then
    rm -f "$tmpdir"/*.log "$tmpdir"/fifo
    rmdir "$tmpdir" || true
  fi
  exit $@
}

function usage() {
  echo "Usage $0 <cnf-file>"
  echo "  Invokes cadical in parallel to lrat_isa"
  exit_cleanup 1
}

function error() {
  echo "c ERROR $@"
  exit_cleanup 1
}


[[ $# == 1 ]] || usage

cnf="$1"
shift

# Create FIFO
tmpdir=$(mktemp -d tmpdir-XXXXXXXXXX) || error "creating temporary directory"
fifo="$tmpdir/fifo"
mkfifo "$fifo" || error "creating named pipe"

# Run solver and checker in parallel
solver_log="$tmpdir/solver.log"
checker_log="$tmpdir/checker.log"

$SOLVER -q --lrat "$cnf" "$fifo" | tee "$solver_log" || true  &
$CHECKER "$cnf" "$fifo" > "$checker_log" || true

# Wait until both finished
wait

# See what happened
if grep -q "^s SATISFIABLE" "$solver_log"; then
  # echo "s SATISFIABLE"
  exit_cleanup 10
elif grep -q "^s VERIFIED UNSAT" "$checker_log"; then
  echo "s VERIFIED UNSAT"
  exit_cleanup 20
elif grep -q "^s UNSATISFIABLE" "$solver_log"; then
  cat "$checker_log"
  echo "c Solver proved UNSAT, but checker failed to verify"
  echo "c Consider using lrat_isa_dbg to get more information about the checker error"
  echo "c If you suspect the problem in the solver, use lrat-trim which has more detailed error messages"
  # echo "s UNSATISFIABLE"
  # echo "c (not certified)"
  exit_cleanup 1
else
  echo "c Solver did not produce an answer"
  exit_cleanup 1
fi

