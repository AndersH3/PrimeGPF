# Verification record and scope

During this conversation, `lake build PrimeGPF.PrimeExponent` completed
successfully with Lean 4.19.0, mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b.
The subsequent PrimeExponentAudit.lean check printed all 11 theorem dependencies;
every list was a subset of {propext, Classical.choice, Quot.sound}.

The successful tool output recorded:

```
Built PrimeGPF.PrimeExponent
Build completed successfully.
PASS: module compiled; 11 theorems use only the allowed foundational axioms.
ZsigmondyInput is discharged. PrimeAPInput remains unproved.
```

This is a transcription of the visible tool output, not a recovered raw log.
The workspace subsequently reverted to an older snapshot. The deliverable's
proof source was recovered verbatim from the source printed alongside that
successful output. The original raw logs and compiler installation were lost.
No fabricated raw log or local-success stamp is included.

The validation checkout used project dependency modules fetched at GitHub commit
4b0f848c99777fc5f0e088b4bb2b80dd458a09e4. Its Core import of all of Mathlib was
replaced by a smaller explicit list of mathlib imports to limit cache downloads;
mathematical declarations and proofs were unchanged. A runtime compatibility
shim corrected the compiler executable path lookup in the container. It did not
change Lean's kernel or any proof rule.

This was a build of the new module and its dependency closure, not of the user's
entire unpublished local checkout. Run verify_prime_exponent.sh after extracting
the patch to obtain fresh raw build/audit logs and the matching integration stamp.

The new module has one harmless unused-tactic warning for `push_cast`. Existing
Core and Dynamics modules also emitted style warnings.
