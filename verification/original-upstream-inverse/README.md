# Current verified official inverse closure

Verified source coverage is the dependency-closed union of **1,159 OAI modules**:
the unchanged 1,042-module historical certificate plus 117 cumulative additions
(54 previously committed and 63 added in this stage). The full AxisCompression
endpoint and original StrongConjecture remain unfinished.

The current **975-module** recovery stage has consistent strict source-build
records and a successful unified kernel/axiom audit with Lean 4.32.2, initial
autoImplicit=false and --trust=0. It counted **21,682 unique declarations** from
**21,691 records**, using only propext, Classical.choice and Quot.sound. Source
and compiled-artifact SHA-256 hashes stayed unchanged across the audit; all 975
independently recomputed source Lake hashes matched recorded inputs.

The 975 comprise 858 unchanged historical-base modules and all 117 cumulative
additions. The other 184 retain historical evidence and were not fresh audit
targets. The historical certificate's 20,689 declaration records are not a new
unique count; do not add overlapping historical and current audit counts.
There are zero replacements relative to the previous 1,137-source OAI tree.
The new whole OAI inventory is 1,200, including 41 modules outside this closure.

Round5 ended at its 80-minute limit with real whole-command timeout exit124.
Of 976 observed artifacts, Lattices.StrideSelectedResidueBadProduct lacked a
completed trace and was excluded; **975 is the authoritative frozen selection**.
Round4 also has recorded timeout exit124. Old rounds1–3 retain unknown whole-
command exit status. The source-evidence collector's exit3 reflects only those
old whole-command gaps, with zero pending selected-module evidence. Local
records and source-only 64-bit Lake hashes do not independently prove exact
source-to-binary correspondence; external dependencies were not independently
replayed.

## Reproduce

Use the repository's pinned Lean 4.32.2 and mathlib revision. Read-only check:

    python3 verification/original-upstream-inverse/replay-current.py

New build and trust-zero audit of exactly the current 975 targets:

    python3 verification/original-upstream-inverse/replay-current.py --run

The script uses LEAN_NUM_THREADS=1; the audit also uses -j1, --trust=0 and
-DautoImplicit=false. It needs only repository sources, the preserved historical
manifest and pinned dependencies, not any temporary recovery directory or full
upstream clone. The old manifest.json, modules.txt and CheckAxioms.lean remain
unchanged. current-replay.json stores the cumulative 117-source delta and exact
target names without duplicating the 1,042 historical source entries or
uploading raw setup/trace archives.

The 63 new files comprise 38 exact sources from OpenAI commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a and 25 compatibility ports with
file-level modification notices. Existing full Apache-2.0 license and
attribution remain under dependencies/openai-finite-szemeredi. Historical
prepared_uncompiled comments are retained verbatim to preserve frozen hashes;
current verification status is recorded in the manifest. This is not an
all-history publication license clearance.

The actual AxisCompression closure is 2,102 modules, including two compatibility
modules beyond the pinned official 2,100-module closure. The full endpoint,
interval adapter, canonical integration and original-target replay remain
unfinished. The repository remains private.
