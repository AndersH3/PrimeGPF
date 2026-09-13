# Fix for the reported Core.lean compilation errors

The user's Lean 4.19.0 build successfully installed mathlib but failed on
three proof blocks in Core.lean (old lines 106, 134 and 166).

A nested `have ... := by omega; simp_all` parsed the trailing tactic into
the inner proof. It ran after omega had already closed that inner goal,
while the outer contradiction remained unfinished.

The three blocks now use explicit multiline proofs, named zero equalities,
rewriting in the relevant hypothesis, and a final omega contradiction.
The same defect was repaired in two blocks in Elementary.lean (old lines
166 and 226), before the next module is compiled.

No theorem statements or mathematical dependencies were changed.
Static source checks passed. These fixes have NOT been compiler-verified
in the authoring environment. Additional downstream errors may remain.

From the existing prime_gpf_lean directory, after downloading the archive:

```bash
unzip -o ~/Downloads/prime_gpf_lean_corefix.zip -d ..
./verify.sh
```

Extraction preserves the existing .lake directory and lake-manifest.json;
they are absent from this source archive. No dependency reinstallation or
clean build is required. If compilation stops again, supply evidence/build.log.
