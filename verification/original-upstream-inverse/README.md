# Current verified official inverse closure

Verified source coverage is the dependency-closed union of **1,432 OAI modules**:
the unchanged 1,042-module historical certificate plus 390 cumulative additions
(332 previously committed and 58 added in this stage). The full AxisCompression
endpoint and original StrongConjecture remain unfinished.

The current **1,365-module** recovery stage has consistent strict source-build
records and a successful unified kernel/axiom audit with Lean 4.32.2, initial
autoImplicit=false and --trust=0. It counted **28,412 unique declarations** from
**28,429 records**, using only propext, Classical.choice and Quot.sound. Source
and compiled-artifact SHA-256 hashes stayed unchanged across the audit; all
1,365 independently recomputed source Lake hashes matched recorded inputs.

The 1,365 comprise 975 unchanged historical-base modules and all 390 cumulative
additions. The other 67 retain historical evidence and were not fresh audit
targets. The historical certificate's 20,689 declaration records are not a new
unique count; do not add overlapping historical and current audit counts.
There are zero replacements relative to the prior 1,415-source OAI tree. The
new whole OAI inventory is 1,473, including 41 modules outside this closure.

Round8 reached its 80-minute limit with real whole-command timeout exit124.
Rounds4–7 likewise have recorded timeout exits; old rounds1–3 retain unknown
whole-command exit status. The source-evidence collector's actual exit3 reflects
only those old whole-command gaps, with zero pending selected-module evidence.
This is separate from the successful audit. Local records and source-only
64-bit Lake hashes do not independently prove exact source-to-binary
correspondence; external dependencies were not independently replayed.

## Reproduce

Use the repository's pinned Lean 4.32.2 and mathlib revision. Read-only check:

    python3 verification/original-upstream-inverse/replay-current.py

New build and trust-zero audit of exactly the current 1,365 targets:

    python3 verification/original-upstream-inverse/replay-current.py --run

The script uses LEAN_NUM_THREADS=1; the audit also uses -j1, --trust=0 and
-DautoImplicit=false. It needs only repository sources, the preserved historical
manifest and pinned dependencies, not a temporary recovery directory or full
upstream clone. Old manifest.json, modules.txt and CheckAxioms.lean remain
unchanged. current-replay.json stores the cumulative 390-source delta and exact
target names without duplicating historical source entries or uploading raw
setup/trace archives. Both retained license files are hash-checked.

## Sources and attribution

The 58 new files comprise 44 exact sources from OpenAI commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a, 13 compatibility ports with
file-level notices, and one separately sourced official mathlib backport.
Existing full Apache-2.0 license and OpenAI attribution remain under
dependencies/openai-finite-szemeredi.

Compatibility.ExteriorPowerInnerProduct comes from leanprover-community/mathlib4
commit d13f23b723b8a846827a245b89c10fc7d3f11612. It retains the complete
ExteriorPower.lean source (Justus Springer, copyright2026) and adds the unchanged
GramMatrix.lean lines137–140 lemma (Peter Pfaffelhuber, copyright2025), with
context and a modification notice. Original copyright headers, fixed source
Git blobs and SHA-256 hashes are recorded in current-replay.json. The complete
upstream Apache-2.0 text is copied verbatim to
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
