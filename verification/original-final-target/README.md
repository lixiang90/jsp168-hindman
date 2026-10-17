# Final target verification — completed checks and reproduction

The final target is **`Hindman168.JSP000168`** at proof source
`7ae70219fb4034899c6c2d23cc3b58ec6730a1ba`. The complete target build,
endpoint exact-type checks, all-local-declaration axiom audit, scope parser and
fresh Lean-kernel replay returned actual exit **0** on 2026-10-17. The whole
suite finished at `13:19:08.112199 UTC`, with all source/environment checks
passed and all 38,290 recorded proof artifacts unchanged.

[Complete evidence](verified-2026-10-17/README.md) is committed at E1
`8ccf3ec0f2d69a7c665a2fb76a6385a1053f6c31`. Its [index](verified-2026-10-17/archive-index.json)
preserves raw/stored hashes and byte lengths; original results are not rewritten.
The actual audit covered 5,066 local modules, 70,418 records and 70,306 unique
names, with only `propext`, `Classical.choice` and `Quot.sound` observed.

The old aggregate `Hindman168` does not import this final chain. Earlier prepared
inventories and component reports below remain historical; the archived final
manifest and results supersede them for P. The original snapshot/upstream replay
manifests remain unchanged. Reproduction uses the pinned Lean 4.32.2/mathlib
inputs; actual verification used incremental artifacts and official pinned
caches. Fresh replay uses the same Lean kernel for safe, nonpartial constants,
skipping unsafe/partial constants. It is not an independent kernel or a
cache-free dependency rebuild, mathematical peer review or award decision.

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

Explicitly select a fresh output directory to also generate `source-closure.json`,
`modules.txt`, and `CheckAllDeclarations.lean`:

```powershell
python verification/original-final-target/prepare.py --output-dir verification-local/final-target-metric-2026-10-17
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

The isolated [audit mechanism self-test](audit-self-test/README.md) records
executed tiny fixtures on the pinned Lean version. It confirms that this
non-`module` audit sees unused private declarations and rejects their deliberately
unapproved test axioms, and that endpoint type locks detect omitted premises.
Those fixtures are outside the proof target's import closure. Their successful
self-test does not establish that the final JSP target builds or passes its audit.

The [direct menu compilation record](menu-direct-check-2026-10-17.json) reports
exit 0 for the conditional menu bridge at its exact source hash. It checks the
explicit metric-topology observable construction against existing dependency
artifacts. It is neither the full target build nor its axiom audit/kernel replay.

The generation script invokes neither Lake nor Lean. Its JSON status is always
preparation, with compilation, axiom-audit execution and kernel replay marked
false. Regenerate the inventory after any source change. Different existing
generated files are preserved unless `--replace-prepared` is explicitly supplied;
keep completed verification evidence in a separate directory.

The dated [metric-adapter source scan](static-source-scan-metric-2026-10-17.json)
records an executed lexical review of all 5,066 local sources at its specified
source-inventory hash. The subsequent [finite-budget checkpoint scan](static-source-scan-finite-budgets-2026-10-17.json)
covers the two local budget additions, the explicit Mathlib series import, and
the public verification tools at source commit `5eede9c`. It again reports no
primary or reduction-oracle findings; all 137 options are classified.
The earlier `static-source-scan-2026-10-17.json` retains
the preceding checkpoint's record.
The separate scanner checks exact source bytes, removes comments and strings,
and classifies the detected proof-input tokens and elaboration options.
After generating an inventory, reproduce a read-only scan with:

```powershell
python verification/original-final-target/static-source-scan.py --manifest verification-local/final-target-metric-2026-10-17/source-closure.json
```

This source-only review did not execute Lean or Lake. Its zero placeholder and
axiom-command counts do not establish that the final theorem builds, has no
hidden hypotheses, or passes its axiom audit and kernel replay. External
boundary sources remain outside the lexical scan.

After the actual dependency build is ready, run these separately using the
repository's pinned toolchain and dependencies, and save each real exit status:

```powershell
$env:LEAN_NUM_THREADS = '3'
lake build Hindman168.JSP000168
$env:LEAN_NUM_THREADS = '1'
lake env lean -j1 --trust=0 -DautoImplicit=false verification/original-final-target/CheckEndpoint.lean
lake env lean -j1 --trust=0 -DautoImplicit=false verification-local/final-target-metric-2026-10-17/CheckAllDeclarations.lean
lake env leanchecker --fresh --verbose Hindman168.JSP000168
```

The committed suite and log parser below have completed on the selected final
target; see the archived actual results above. The suite records the three verification commands' real exits and
compares source, artifact, dependency and toolchain-binary inputs before/after.
It does not run or replace the complete `lake build Hindman168.JSP000168`;
retain that build's actual successful exit separately before starting the suite.
Generate a fresh inventory after any verification-tool change: the inventory
also binds the suite, parser and static scanner by SHA256.

For a new reproduction checkpoint, choose fresh inventory and suite directories:

```powershell
python verification/original-final-target/prepare.py --output-dir verification-local/final-target-repro
# Run only after separately recording the complete target build's exit 0:
python verification/original-final-target/run-final-suite.py verification-local/final-target-repro/source-closure.json final-target-suite-repro
python verification/original-final-target/summarize-audit.py verification-local/final-target-repro/source-closure.json verification-local/final-target-suite-repro/02.log --output verification-local/final-target-suite-repro/audit-summary.json
```

The suite's second positional argument is a new directory name below
`verification-local`. The parser independently checks every logged declaration,
per-module and global counts, the exact manifest module set, and the three-axiom
allowlist. It supports wrapped pretty printing and rejects incomplete logs;
its successful parse does not replace the suite's real exits or kernel replay.
The parser is read-only unless a new report path is explicitly supplied.

Axiom inspection of imported artifacts and a fresh kernel replay are distinct
checks. The pinned Lean `leanchecker --fresh` replays safe, nonpartial target/imported
constants into a fresh checking environment (skipping unsafe/partial constants) using Lean's own kernel; it is not a separate
kernel implementation. Pair that replay with a source rebuild and record source
and artifact hashes before and after checking. Do not reuse this prepared
inventory as evidence for a changed source checkpoint. The original preparation records did not claim execution; the completed final
results are linked at the top of this page.
