# Pinned upstream API sources

Source files were inspected at mathlib **v4.19.0**, commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`.
This was source inspection, not Lean compilation. No upstream source files
have been vendored into this package.

- [Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean](https://github.com/leanprover-community/mathlib4/blob/v4.19.0/Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean) — Git blob `d09b570d395c7945e9c5d303f9c6524d6b498ee8`.
- [Mathlib/GroupTheory/OrderOfElement.lean](https://github.com/leanprover-community/mathlib4/blob/v4.19.0/Mathlib/GroupTheory/OrderOfElement.lean) — Git blob `0ae783d8b8a6ad6a91f9ee6bb32776fca9c4e914`.
- [Mathlib/Data/ZMod/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/v4.19.0/Mathlib/Data/ZMod/Basic.lean) — Git blob `b5e25c345f2ada49f51c4dd78d5e2d06ea9e238c`.
- [Mathlib/NumberTheory/LegendreSymbol/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/v4.19.0/Mathlib/NumberTheory/LegendreSymbol/Basic.lean) — Git blob `c10ead69e7f18ef5dd76f78f101c0f65acc6136c`.
- [Mathlib/FieldTheory/Finite/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/v4.19.0/Mathlib/FieldTheory/Finite/Basic.lean) — Git blob `6e9a844f1180d9066437f53715b02b966de2dbc5`.
- [Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/v4.19.0/Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/Basic.lean) — Git blob `2d4ba7f18f74bf89123b9eb4449d7eed1d6304ab`.
- [Mathlib/NumberTheory/LSeries/PrimesInAP.lean](https://github.com/leanprover-community/mathlib4/blob/v4.19.0/Mathlib/NumberTheory/LSeries/PrimesInAP.lean) — Git blob `2c37aa8e73f38528dd70a405be1aac841510f691`.

The proof extension uses standard finite-field order, quadratic-character,
quadratic-reciprocity and Dirichlet-prime-existence APIs. It does not assume
the missing Zsigmondy or prime-number-theorem inputs from these references.
