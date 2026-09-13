#!/usr/bin/env bash
set -euo pipefail

# One-command verification for the Prime-GPF Agda port.
#
# Checks, in order:
#   1. Core module type-checks.
#   2. Fast compile-time regression proofs type-check.
#   3. The 5x5 power-table runtime test compiles with GHC (-O0) and passes.
#
# Intended environment:
#   Agda 2.8.0
#   agda-stdlib 2.3
#   GHC available on PATH

cd -- "$(dirname -- "${BASH_SOURCE[0]}")"

EXPECTED_RUNTIME_OUTPUT='PASS: gpfPowerTableValues 5 matches the expected PARI/GP table.'

stage() {
  printf '\n============================================================\n'
  printf '%s\n' "$1"
  printf '============================================================\n'
}

fail() {
  printf '\nVERIFY FAILED: %s\n' "$1" >&2
  exit 1
}

command -v agda >/dev/null 2>&1 || fail "agda is not installed or not on PATH"
command -v ghc  >/dev/null 2>&1 || fail "ghc is not installed or not on PATH"

stage "Environment"
agda --version
ghc --version

stage "1/3  Type-check core PrimeGPF.agda"
/usr/bin/time -v agda PrimeGPF.agda
printf 'PASS: PrimeGPF.agda type-checks.\n'

stage "2/3  Run fast compile-time regression proofs"
/usr/bin/time -v agda PrimeGPFTests.agda
printf 'PASS: PrimeGPFTests.agda type-checks.\n'

stage "3/3  Compile and run 5x5 runtime regression test"
# -O0 is intentional: the test executes essentially instantly, while disabling
# GHC optimization considerably reduces first-build compilation work.  Agda's
# generated MAlonzo/ .o files are left in place so later runs can reuse them.
/usr/bin/time -v agda --compile --ghc-flag=-O0 PrimeGPFRuntimeTestsMinimal.agda

[[ -x ./PrimeGPFRuntimeTestsMinimal ]] || \
  fail "compiled executable PrimeGPFRuntimeTestsMinimal was not produced"

runtime_output="$(./PrimeGPFRuntimeTestsMinimal)"
printf '%s\n' "$runtime_output"

[[ "$runtime_output" == "$EXPECTED_RUNTIME_OUTPUT" ]] || \
  fail "runtime 5x5 table comparison did not return the expected PASS result"

printf '\n============================================================\n'
printf 'ALL PRIME-GPF AGDA CHECKS PASSED\n'
printf '============================================================\n'
