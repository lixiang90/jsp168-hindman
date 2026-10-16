# Current verified official inverse closure

The verified source coverage is now the dependency-closed union of **1,057 OAI
modules**: the previous 1,042-module certificate plus 15 new source modules.
The original StrongConjecture and full AxisCompression endpoint remain unfinished.

The current recovery replay strictly compiled and kernel/axiom-checked 751 modules
with Lean 4.32.2, `autoImplicit=false` and `--trust=0`: **17,823 unique declarations**
(17,830 audit records), using only `propext`, `Classical.choice`, and `Quot.sound`.
Of these, 736 exactly match the previous certificate and 15 are new. The remaining
306 modules retain their historical certificate; they were not freshly replayed
in this stage. The historical 20,689 count denotes audit records, not a new
unique-declaration total. Do not add overlapping audit counts.

The pinned official AxisCompression import closure contains 2,100 modules. The
current port adds two proved compatibility modules, `TensorInduction` and
`ExteriorPowerInnerProduct`, so its full actual closure contains 2,102 modules.
This partial checkpoint does not verify the whole endpoint.

## Reproduce

Use the repository's pinned Lean 4.32.2 and mathlib revision. The current replay
manifest and script record the exact 751 targets, source hashes and commands.
The original `manifest.json`, `modules.txt`, and `CheckAxioms.lean` preserve the
previous 1,042-module certificate unchanged. See `current-replay.json` for the
source coverage union and the distinction between historical and fresh checks.

Source and compiled-artifact SHA-256 hashes stayed unchanged across the new audit.
Each current source's Lake text hash was independently recomputed and matched its
recorded compiler input hash. Interrupted overall build runs have unknown final
exit status; completed per-module strict build records and the separate successful
kernel audit are recorded explicitly. Lake's 64-bit hashes are not cryptographic
source-to-binary proofs.

Official source is pinned to OpenAI commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. New compatibility changes carry source
notices; license and attribution files remain under
`dependencies/openai-finite-szemeredi`. The finite native geometric menu and exact
same-step linearization are recorded separately in
[the geometric layer](../original-native-geometric-layer/README.md).

The remaining analytic closure, interval adapter, canonical imports and full
original-target replay still have to pass. The repository remains private.
