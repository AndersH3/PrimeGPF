# Prime GPF — Agda computational port

Certificate-preserving Agda translation of the PARI/GP routines
`greatestPrimeFactor`, `gpfPlus`, `gpfTimes`, `gpfPower`, `primePrefix`,
`gpfPowerTable`, and `fiberTimes`.

## Type hierarchy

```text
P ⊆ N ⊆ ℕ
```

`N` is the subtype of naturals greater than 1, and `P` is the subtype of
certified primes.  The central types are:

```agda
greatestPrimeFactor : N → P
gpfPlus             : P → P → P
gpfTimes            : P → P → P
gpfPower            : P → P → P
```

## Verified environment

The project has been tested with:

- Agda 2.8.0
- agda-stdlib 2.3
- Fedora 44 Toolbox
- GHC backend

## One-command verification

From this directory:

```bash
./verify.sh
```

The script deliberately performs three independent checks:

1. `agda PrimeGPF.agda` — core type checking.
2. `agda PrimeGPFTests.agda` — fast compile-time regression proofs using
   definitional equality (`refl`).
3. Compiles `PrimeGPFRuntimeTestsMinimal.agda` with the GHC backend using
   `-O0`, then executes it and requires the exact 5×5 PARI/GP-table PASS
   result.

A successful run ends with:

```text
ALL PRIME-GPF AGDA CHECKS PASSED
```

The generated `MAlonzo/` directory and object files are intentionally retained
so subsequent `./verify.sh` runs can reuse GHC compilation artifacts.

## Heavy proof-normalization test

`PrimeGPFHeavyTests.agda` is retained for reference but is **not** run by
`verify.sh`. It proves the 5×5 table using `refl`, which forces large certified
factorisations during Agda type checking and is much slower than the compiled
runtime regression test.
