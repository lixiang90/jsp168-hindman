# Final target verification — prepared, not executed

The verification target is **`Hindman168.JSP000168`**. The old root module
`Hindman168` does not import this final proof chain and cannot stand in for it.
This directory prepares checks; it does not certify successful compilation,
an unconditional proof, publication or an award submission. The original
snapshot and upstream replay manifests remain unchanged.

`CheckEndpoint.lean` imports the new target and checks the key declarations from
`OriginalNativeIntervalInverseMenu`, `OriginalNativeIntervalInverse`,
`FinalStrongFromOpenAI`, and `JSP000168`. It prints their full types and axiom
dependencies. Transparent proposition equality checks using `rfl` compare the
explicit positive, exact-cardinality finite-set theorem, the inverse family,
and the fully expanded strong theorem with their actual theorem types. These
checks are intended to expose any remaining hidden premise or binder.

The read-only command below discovers the actual import closure of the target
under the local namespaces `Hindman168`, `OAI`, and `PrimeNumberTheoremAnd`:

```powershell
python verification/original-final-target/prepare.py
```

Explicitly select a new output directory to also generate `source-closure.json`,
`modules.txt`, and `CheckAllDeclarations.lean`:

```powershell
python verification/original-final-target/prepare.py --output-dir verification-local/final-target-2026-10-17
```

The inventory hashes every local source in that closure and records each import.
Imports crossing into other namespaces, including Mathlib and Lean, are listed
and counted as external boundaries; their sources are not recursively inventoried
or hash-verified by this script. The generated non-module audit visits **all**
declaration records of every inventoried module, including internal/private
declarations, and checks every declaration's transitive axiom dependencies against
`propext`, `Classical.choice`, and `Quot.sound`. It does not sample selected
theorems. Declarations in external boundary modules that are unused by these
targets are outside that declaration-listing scope.

The generation script invokes neither Lake nor Lean. Its JSON status is always
preparation, with compilation, axiom-audit execution and kernel replay marked
false. Regenerate the inventory after any source change. Different existing
generated files are preserved unless `--replace-prepared` is explicitly supplied;
keep completed verification evidence in a separate directory.

The dated `static-source-scan-2026-10-17.json` records an executed lexical
review of all 5,066 local sources at its specified source-inventory hash.
The separate scanner checks exact source bytes, removes comments and strings,
and classifies the detected proof-input tokens and elaboration options.
After generating an inventory, reproduce a read-only scan with:

```powershell
python verification/original-final-target/static-source-scan.py --manifest verification-local/final-target-2026-10-17/source-closure.json
```

This source-only review did not execute Lean or Lake. Its zero placeholder and
axiom-command counts do not establish that the final theorem builds, has no
hidden hypotheses, or passes its axiom audit and kernel replay. External
boundary sources remain outside the lexical scan.

After the actual dependency build is ready, run these separately using the
repository's pinned toolchain and dependencies, and save each real exit status:

```powershell
lake build Hindman168.JSP000168
lake env lean -j1 --trust=0 -DautoImplicit=false verification/original-final-target/CheckEndpoint.lean
lake env lean -j1 --trust=0 -DautoImplicit=false verification-local/final-target-2026-10-17/CheckAllDeclarations.lean
lake env leanchecker --fresh --verbose Hindman168.JSP000168
```

Axiom inspection of imported artifacts and a fresh kernel replay are distinct
checks. The pinned Lean `leanchecker --fresh` replays the target and its imported
constants into an empty environment using Lean's own kernel; it is not a separate
kernel implementation. Pair that replay with a source rebuild and record source
and artifact hashes before and after checking. Do not reuse this prepared
inventory as evidence for a changed source checkpoint. No execution of the above
Lean commands is claimed by this directory's initial contents.
