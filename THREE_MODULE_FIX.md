# Three-module proof repair

Apply from your existing prime_gpf_lean project directory:

```bash
unzip -o ~/Downloads/prime_gpf_lean_three_module_fix.zip -d .
./verify.sh
```

This patch contains only SmallFibers.lean, Orders.lean, DirectExponential.lean,
this note, and a unified diff. It preserves your earlier Core, Elementary,
Arithmetic, and Quadratic fixes and all theorem statements.

Changes:
- SmallFibers: expose the concrete kernel and supply n explicitly for both
  exponent bounds; expand the modulo-three sum and split the two possible
  nonzero prime residues before the modulo-six conclusion.
- Orders: replace recursive simplification with a congrArg calculation,
  applying the supplied congruence once.
- DirectExponential: prove the coefficient identity first and rewrite the
  power addition at the explicitly specified exponent.

Validation: checked that all theorem headers in these three files are unchanged
and that no sorry, admit, axiom, or native_decide token was introduced.
These checks are not Lean compilation or proof validation. A Lean 4.19.0
release was downloaded, but its executable exits with "failed to locate
application" in this environment. Lake exits with "could not detect the
configuration of the Lake installation". No Lean compiler check was completed.
The remaining modules and missing mathematical dependencies are not resolved
by this patch. Run the full existing verify.sh locally. Its documented exit 2
after successful build/audit means the formalization still has open entries;
exit 1 with Lean errors means the build failed.
