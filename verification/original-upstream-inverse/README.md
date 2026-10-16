# Current verified official inverse closure

Verified source coverage is the dependency-closed union of **1,482 OAI modules**:
the unchanged 1,042-module historical certificate plus 440 cumulative additions
(390 previously committed and 50 added in this stage). The full AxisCompression
endpoint and original StrongConjecture remain unfinished.

The current **1,415-module** recovery stage has consistent strict source-build
records and a successful unified kernel/axiom audit with Lean 4.32.2, initial
autoImplicit=false and --trust=0. It counted **29,363 unique declarations** from
**29,382 records**, using only propext, Classical.choice and Quot.sound. Source
and compiled-artifact SHA-256 hashes stayed unchanged across the audit; all
1,415 independently recomputed source Lake hashes matched recorded inputs.

The 1,415 comprise 975 unchanged historical-base modules and all 440 cumulative
additions. The other 67 retain historical evidence and were not fresh audit
targets. The historical certificate's 20,689 declaration records are not a new
unique count; do not add overlapping historical and current audit counts.
There are zero replacements relative to the prior 1,473-source OAI tree. The
new whole OAI inventory is 1,523, including 41 modules outside this closure.

Round9 reached its 80-minute limit with real whole-command timeout exit124.
Rounds4–8 likewise have recorded timeout exits; old rounds1–3 retain unknown
whole-command exit status. The source-evidence collector's actual exit3 reflects
only those old whole-command gaps, with zero pending selected-module evidence.
This is separate from the successful audit. Local records and source-only
64-bit Lake hashes do not independently prove exact source-to-binary
correspondence; external dependencies were not independently replayed.

## Reproduce

Use the repository's pinned Lean 4.32.2 and mathlib revision. Read-only check:

    python3 verification/original-upstream-inverse/replay-current.py

New build and trust-zero audit of exactly the current 1,415 targets:

    python3 verification/original-upstream-inverse/replay-current.py --run

The script uses LEAN_NUM_THREADS=1; the audit also uses -j1, --trust=0 and
-DautoImplicit=false. It needs only repository sources, the preserved historical
manifest and pinned dependencies, not a temporary recovery directory or full
upstream clone. Old manifest.json, modules.txt and CheckAxioms.lean remain
unchanged. current-replay.json stores the cumulative 440-source delta and exact
target names without duplicating historical source entries or uploading raw
setup/trace archives. Both retained license files are hash-checked.

## Sources and attribution

The 50 new files comprise 35 exact sources from OpenAI commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a and 15 compatibility ports with
file-level notices. Existing full Apache-2.0 license and OpenAI attribution
remain under dependencies/openai-finite-szemeredi.

The previously committed Compatibility.ExteriorPowerInnerProduct backport and
its provenance are retained unchanged. It comes from leanprover-community/mathlib4
commit d13f23b723b8a846827a245b89c10fc7d3f11612, retaining the complete
ExteriorPower.lean source (Justus Springer, copyright 2026) and adding unchanged
GramMatrix.lean lines 137–140 (Peter Pfaffelhuber, copyright 2025), with context
and a modification notice. Both original copyright headers, fixed source Git
blobs and SHA-256 hashes remain in current-replay.json. The exact upstream
Apache-2.0 text remains in
[LICENSE.mathlib-backport](../../dependencies/openai-finite-szemeredi/LICENSE.mathlib-backport).
The pinned mathlib dependency is unchanged. Source retrieval association uses
retained fixed-commit evidence; this preparation adds no new remote authenticity
attestation or repository-wide NOTICE inventory claim.

Historical prepared_uncompiled comments remain verbatim to preserve frozen
hashes; current verification status is recorded in the manifest. This is not an
all-history publication license clearance. The actual AxisCompression closure
contains 2,102 modules, including two compatibility modules beyond the official
2,100-module closure. The full endpoint, interval adapter, canonical integration
and original-target replay remain unfinished. The repository remains private.
