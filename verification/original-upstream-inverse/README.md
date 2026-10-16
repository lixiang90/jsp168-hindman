# Current verified official inverse closure

Verified source coverage is the dependency-closed union of **1,096 OAI modules**:
the preserved 1,042-module historical certificate plus 54 cumulative additions
(15 previously committed and 39 added in this stage). The original
StrongConjecture and full AxisCompression endpoint remain unfinished.

The current recovery stage has consistent strict source-build records for all
912 selected modules and a successful unified kernel/axiom audit with Lean
4.32.2, initial autoImplicit=false and --trust=0. The audit counted **19,983 unique
declarations** from **19,992 records**, using only propext, Classical.choice and
Quot.sound. Source and compiled-artifact SHA-256 hashes stayed unchanged across
the audit. Independently recomputed source Lake hashes matched all 912 recorded
compiler inputs.

These 912 comprise 858 unchanged historical-base modules, all 15 previous
additions and 39 new sources. The other 184 modules retain historical evidence;
they were not fresh audit targets. There are no replacements relative to the
previous committed 1,098-source OAI tree. The new complete OAI source inventory
is 1,137; its 41 other modules are outside this inverse-closure certificate.

The previous 751-module audit counted 17,823 unique declarations from 17,830
records. The old 1,042-module certificate reported 20,689 declaration records,
not a newly established unique count. Do not add overlapping audit counts.

Round4 had an 80-minute limit and ended with whole-command timeout exit124.
That unsuccessful full AxisCompression command is distinct from the completed
selected-module records and successful separate audit. Old interrupted rounds
1–3 still have unknown whole-command exit status. The source-evidence collector
returned exit3 only for those old whole-command gaps, with no pending selected
module evidence. Lake's source-only 64-bit hashes and local build records are
not cryptographic source-to-binary proofs; external dependencies were not
independently replayed.

The actual port closure contains 2,102 modules, including TensorInduction and
ExteriorPowerInnerProduct beyond the pinned official 2,100-module closure.
This partial checkpoint does not verify the whole endpoint.

## Reproduce

Use this repository's pinned Lean 4.32.2 and mathlib revision. For a read-only
source check, run:

    python3 verification/original-upstream-inverse/replay-current.py

To build and run a new trust-zero audit of exactly the current 912 targets:

    python3 verification/original-upstream-inverse/replay-current.py --run

The script explicitly uses LEAN_NUM_THREADS=1; the audit also uses -j1,
--trust=0 and -DautoImplicit=false. It needs only repository sources, the
preserved historical manifest and pinned dependencies, not a temporary
recovery directory or full upstream clone. The old manifest.json, modules.txt
and CheckAxioms.lean remain unchanged. current-replay.json records the cumulative
54-source delta, exact current targets and evidence hashes without duplicating
the historical 1,042 source entries or uploading raw setup/trace archives.

Official source is pinned to OpenAI commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a. The 39 new files comprise 29 exact
upstream files and 10 compatibility ports with file-level modification notices.
Existing full Apache-2.0 license and attribution remain under
dependencies/openai-finite-szemeredi. Historical prepared_uncompiled source
comments are retained verbatim to preserve frozen hashes; current verification
status is recorded in the manifest. This is not an all-history publication
license clearance.

The remaining analytic closure, interval adapter, canonical integration and
full original-target replay still have to pass. The repository remains private.
