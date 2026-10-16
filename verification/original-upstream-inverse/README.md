# Current verified official inverse closure

Verified source coverage is the dependency-closed union of **1,310 OAI modules**:
the unchanged 1,042-module historical certificate plus 268 cumulative additions
(117 previously committed and 151 added in this stage). The full AxisCompression
endpoint and original StrongConjecture remain unfinished.

The current **1,217-module** recovery stage has consistent strict source-build
records and a successful unified kernel/axiom audit with Lean 4.32.2, initial
autoImplicit=false and --trust=0. It counted **26,033 unique declarations** from
**26,047 records**, using only propext, Classical.choice and Quot.sound. Source
and compiled-artifact SHA-256 hashes stayed unchanged across the audit; all
1,217 independently recomputed source Lake hashes matched recorded inputs.

The 1,217 comprise 949 unchanged historical-base modules and all 268 cumulative
additions. The other 93 retain historical evidence and were not fresh audit
targets. The historical certificate's 20,689 declaration records are not a new
unique count; do not add overlapping historical and current audit counts.
There are zero replacements relative to the prior 1,200-source OAI tree. The
new whole OAI inventory is 1,351, including 41 modules outside this closure.

Round6 reached its 80-minute limit with real whole-command timeout exit124.
Rounds4 and5 likewise have recorded timeout exits; old rounds1–3 retain unknown
whole-command exit status. The source-evidence collector's exit3 reflects only
those old whole-command gaps, with zero pending selected-module evidence. This
is separate from the successful audit. Local records and source-only 64-bit
Lake hashes do not independently prove exact source-to-binary correspondence;
external dependencies were not independently replayed.

## Reproduce

Use the repository's pinned Lean 4.32.2 and mathlib revision. Read-only check:

    python3 verification/original-upstream-inverse/replay-current.py

New build and trust-zero audit of exactly the current 1,217 targets:

    python3 verification/original-upstream-inverse/replay-current.py --run

The script uses LEAN_NUM_THREADS=1; the audit also uses -j1, --trust=0 and
-DautoImplicit=false. It needs only repository sources, the preserved historical
manifest and pinned dependencies, not a temporary recovery directory or full
upstream clone. Old manifest.json, modules.txt and CheckAxioms.lean remain
unchanged. current-replay.json stores the cumulative 268-source delta and exact
target names without duplicating historical source entries or uploading raw
setup/trace archives.

The 151 new files comprise 112 exact sources from OpenAI commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a and 39 compatibility ports with
file-level modification notices. Existing full Apache-2.0 license and
attribution remain under dependencies/openai-finite-szemeredi. Historical
prepared_uncompiled comments are retained verbatim to preserve frozen hashes;
current verification status is recorded in the manifest. This is not an
all-history publication license clearance.

The actual AxisCompression closure contains 2,102 modules, including two
compatibility modules beyond the pinned official 2,100-module closure. The full
endpoint, interval adapter, canonical integration and original-target replay
remain unfinished. The repository remains private.
