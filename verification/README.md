# Verification overview — current checkpoint

**Checkpoint, 2026-10-17; final validation remains incomplete.** The explicit final
target has a real successful complete build, endpoint check and all-local-
declaration axiom audit. Fresh kernel replay, the whole suite's real exit and
its final before/after artifact comparison are still **PENDING**. No public
archive, evidence commit E1, publication or award submission is asserted.
The [dated checkpoint evidence](original-final-target/checkpoint-2026-10-17/README.md) preserves actual completed checks and a fixed running-suite snapshot.

## Current final target and checked source scope

The selected proof commit is **`7ae70219fb4034899c6c2d23cc3b58ec6730a1ba`**. Build
**`Hindman168.JSP000168`** explicitly: the old default aggregate `Hindman168`
and `Verification.lean` do not import this new final chain. The source route is:

1. OpenAI's fixed cyclic inverse in
   [AxisCompression](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AxisCompression.lean).
2. The local [menu bridge](../Hindman168/OriginalNativeIntervalInverseMenu.lean)
   and [exact interval adapter](../Hindman168/OriginalNativeIntervalInverse.lean),
   preserving step `s` at Gowers order `s + 1`, with the menu and bounds chosen
   before the period, interval and input.
3. [Final strong assembly](../Hindman168/FinalStrongFromOpenAI.lean), supplying
   the inverse family to the existing `strongConjecture_of_native_inverse`.
4. [Explicit JSP168 statement](../Hindman168/JSP000168.lean), with exactly `m`
   distinct positive integers and one color for every nonempty subset sum and
   product. This is the arbitrary finite-size statement, not an infinite set.

The full expanded StrongConjecture quantifies over all `r`, colorings, `m`,
and real `R ≥ 2`, `D ≥ 1`. It produces a strictly increasing positive
`a : Fin m → ℕ` satisfying the strict real-power separation inequality at every
index, and the same one-color conclusion for all nonempty indexed subsets.
The [endpoint locks](original-final-target/CheckEndpoint.lean) compare all
binders of this expanded statement, the finite statement and the universe-0
inverse family using `rfl`; they do not silently apply away a premise.

The manifest covers **5,066** actual local import-closure modules: **2,914
Hindman168**, **2,143 OAI**, **9 PrimeNumberTheoremAnd**. It also binds nine
repository configuration/tool input files and the generated audit. Manifest
SHA256: `9176ef5a4f4d41b796269c88a90e23966ca62b17bef2a68060b12125886b9b7e`. Source-inventory SHA256: `dcf81b5e67766bba2d3bb3f3cc1455e75940a47301e1f79efa9171f96d003796`.
Generated audit SHA256:
`eec469be1953dbcebd8ec20a8c5d4981c6427e999579764c287e4eae8e5e8783`.
The 629 unique direct external imports and 2,174 crossing edges are recorded
boundaries; their transitive sources are not recursively inventoried here.

## Actual results so far

| Check | Recorded outcome |
| --- | --- |
| Complete `lake -v build Hindman168.JSP000168` | Actual Lake **exit0** and source-bound wrapper **exit0**, **13,720 jobs** |
| Complete build UTC | `11:44:05.740710` → `11:58:57.370689` on 2026-10-17; binding complete `11:59:18.230742` |
| Build source/tool snapshots | Before/after equal byte-for-byte; both SHA256 equal the manifest SHA above |
| Suite 01: endpoint types/axioms | Actual **exit0**, `12:03:58.156654` → `12:04:57.279741` UTC; all three full type locks passed; seven key exports inspected |
| Suite 02: every local declaration record | Actual **exit0**, `12:04:57.281503` → `12:06:11.547739` UTC |
| Complete scope parser | Actual **exit0**, `passed=true`; **5,066 exact module footers**, **70,418 records**, **70,306 unique names**, 95 names shared across modules; no missing/extra/error |
| Observed transitive axioms | Only **propext, Classical.choice, Quot.sound**; these are observed results, not merely the configured allowlist |
| Raw Git bytes at selected commit | Actual **exit0**; 5,066 proof sources + 9 repository inputs + `.gitattributes` all match raw Git/worktree/manifest bytes |
| Current lexical scan | All 5,066 sources; **145 options** classified, no primary or reduction-oracle findings; not a semantic proof |
| Suite before-state | Source/environment gates passed, 9 dependency heads match pins, **38,290** olean/private/server files inventoried |
| Suite 03: `leanchecker --fresh --verbose Hindman168.JSP000168` | **PENDING** real exit and complete log |
| Whole final suite / final artifacts | **PENDING** whole exit, finished UTC, after-state and full before/after equality |
| Public evidence archive / E1 / immutable evidence URLs | **PENDING** |

The actual endpoint log includes:

```text
'Hindman168.strongConjecture_from_openai' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
'Hindman168.jsp000168_from_openai' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

The complete audit records use `Classical.choice` in 58,052 records, `Quot.sound`
in 62,957, and `propext` in 67,414. A declaration may use a subset. The parser
summary SHA256 is
`c0479b3d93d8386bd9c845bf702e2438afb4801e46e1acf010e9af9ff4628d5c`,
bound to actual 02.log SHA256
`4cb628013abad789dc2d6c8dafcf56f930efb871b96bde761c0e3a5d0e4d8158`.

The [dated checkpoint](original-final-target/checkpoint-2026-10-17/README.md) preserves actual build results, source/tool snapshots, endpoint output, the full declaration log, scope parser summary, lexical scan and raw Git binding. Its [index](original-final-target/checkpoint-2026-10-17/checkpoint-index.json) maps original/stored hashes and bytes. The copied suite journal is a fixed **running** snapshot, with no final replay/after-state result. Final archival evidence remains pending. Original result text and paths are not rewritten.

## What these checks cover

The generated non-module audit enumerates every kernel declaration record of
every inventoried local module, including private/internal declarations. It
checks transitive axiom dependencies, including external dependencies used by
those declarations. It does not enumerate unused external declarations. The
[small mechanism self-tests](original-final-target/audit-self-test/README.md)
check private-declaration loading and omitted-premise rejection; their deliberate
negative-test axioms remain outside the proof target and are not JSP evidence.

The separate fresh replay uses the **same pinned Lean kernel** in a fresh
checking environment. It replays safe, nonpartial constants from the target and
its imports, skipping unsafe/partial constants. It is not an independent kernel,
external mathematical peer review, or a source rebuild of Lean/Mathlib. Empty or
buffered stdout while the process runs does not determine its eventual result.
No completion claim follows until the actual third exit and final suite gates.

The successful build used incremental local artifacts and pinned official
dependency caches. No clean/cache-free rebuild of all dependency sources is
claimed. The public suite records three checks and current input stability;
it does not perform or replace the separately recorded complete target build.
The static scanner's 145 options comprise 132 resource-limit settings, nine
meta-level definitional-equality settings, three theorem aliases and one style
linter. Its no-oracle/token finding is lexical and limited to local sources.

Use the public [final-target scripts and instructions](original-final-target/README.md).
Choose new inventory/suite output directories, stop on any nonzero command,
record cache use and real whole exits, and regenerate after any source/tool edit.
Run from the repository root with the committed Lean 4.32.2/mathlib pins:

```powershell
python verification/original-final-target/prepare.py --output-dir verification-local/repro-final
$env:LEAN_NUM_THREADS = '3'
lake -v build Hindman168.JSP000168
# Only after the complete build really exits0:
python verification/original-final-target/run-final-suite.py verification-local/repro-final/source-closure.json repro-suite-final
python verification/original-final-target/summarize-audit.py verification-local/repro-final/source-closure.json verification-local/repro-suite-final/02.log --output verification-local/repro-suite-final/audit-summary.json
```

These reproduction commands are instructions, not another observed successful
run. `lake exe cache get` is cache-based dependency setup; retain the committed
lockfile and do not silently upgrade pins with `lake update`.

## Historical conditional development and component records

The original [3,059-entry manifest](../verification-manifest.json),
[old snapshot verifier](../scripts/verify_snapshot.py), `Hindman168.lean` and
`Verification.lean` preserve an earlier scope. They do not include the new
canonical final endpoint. Their historical evidence is retained rather than
rewritten into final-target evidence.

At the earlier checkpoint, `strongConjecture_of_native_inverse` was a conditional
endpoint whose remaining input was the genuine higher-order native interval
inverse family. Uniform selected Alignment was already unconditional. The new
canonical assembly now supplies that family; its separate final replay remains
pending. The conditional interface itself is still present and mathematically
useful. Its prediction interface fixes genuine native step-bounded linear-orbit
models and positive bounds before the cyclic order, interval and bounded input;
it is not weakened to an input-dependent or higher-step menu.

The earlier final deduction used `principal_product_chain_selection`, then
`principal_final_deduction_tolerances` for finite scales and positive delta,
with tolerances chosen before models and the exact original prediction data/
adding-pair-event liminf. Its positive distinct common-color FS/FP extraction
is recorded in [final deduction](positive-principal-sum/README.md) and
[principal count extraction](principal-count-extraction/README.md).
[Finite-to-strong](finite-to-strong/README.md) records the separation bridge and
`finite_iff_strong`; the old conditional hypotheses remain part of those old
interface theorems rather than being erased from their statements.

The historical [uniform Alignment](uniform-alignment/README.md) interface
chooses finite scales, a common clearing integer and delta before master/model
parameters, with the literal raw law and original alignment event. Retained
component links are [local route coverage](local-route-coverage/README.md),
[pivot extension](pivot-extension/README.md),
[selected gap geometry](selected-gap-geometry/README.md),
[native joint geometry](native-joint-geometry/README.md),
[future thresholds and observables](future-threshold-and-observables/README.md),
[concrete route interfaces](concrete-joint-route-interfaces/README.md),
[principal native mass](principal-native-mass/README.md),
[original recurrence/PET](nilpotent-recurrence/README.md),
[weighted shear laws](weighted-shear-box-laws/README.md), and
[native weighted actions](weighted-shear-native-actions/README.md).

Other historical interfaces include [supported cubes](supported-cube-interface/README.md),
[rooted normalization and U1](interval-rooted-and-one/README.md),
[zero extension](interval-zero-extension/README.md),
[bounded model codes](bounded-model-codes/README.md), and
[coset-cover transport](coset-cover-transport/README.md).
The [same-step algebra](original-same-step-algebra/README.md) records 17 local
modules / 312 official imports; the [native geometric layer](original-native-geometric-layer/README.md)
records twelve new modules and a 553-module/14,338-declaration component audit.
The [inverse normalization](original-inverse-normalization/README.md) records
four modules/54 declarations. Other retained checks are
[inverse building blocks](original-inverse-building-blocks/README.md),
[compact metric control](original-fiber-compact/README.md), and
[BCH fiber metric](original-fiber-bch/README.md).

The [historical upstream subset](original-upstream-inverse/README.md) records a
**1,525-module** coverage union and a **1,469-module** recovery audit with
**30,068 unique declarations / 30,091 records**; 56 other modules retained earlier
evidence. These are overlapping historical counts, not additions to the final
5,066-module audit. The restored [577-source batch](original-upstream-inverse/prepared-axis-2026-10-17.json)
(386 exact / 191 compatibility ports) and 2,102-module Axis closure are also
separate scopes. Old comments saying prepared/uncompiled remain source-history
text; no old report is silently promoted to a new whole-target result.

The root [README](../README.md) retains links to removed historical logs at the
matching pre-cleanup commits. Old scripts may require predecessor records and
original Windows paths. Use a separate matching checkout for historical replay;
do not run them as substitutes for the current final target.

## Attribution and publication boundary

OpenAI receives mathematical solver and upstream Lean source credit at fixed
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`; the older finite-Szemerédi layer
has a separate [source record](../dependencies/openai-finite-szemeredi/SOURCE-MANIFEST.json).
The local Codex-assisted continuation and compatibility/verification work are
reviewable through their own commit history, rather than inferred from account
ownership. Preserve [PNT+ attribution](../PNTPLUS-ATTRIBUTION.txt),
[PNT+ license](../LICENSE-PNTPLUS), the [OpenAI license](../dependencies/openai-finite-szemeredi/LICENSE)
and [Mathlib backport license](../dependencies/openai-finite-szemeredi/LICENSE.mathlib-backport).
No new blanket project license, verified personal identity, sole authorship,
first-proof claim or award/payment conclusion is introduced by this index.
Evidence publication and any awards PR remain PENDING.
