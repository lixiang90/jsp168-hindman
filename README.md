# JSP-000168 / Erdős #172 — Lean formalization

**Final verification completed — 2026-10-17.** At proof commit
`7ae70219fb4034899c6c2d23cc3b58ec6730a1ba`, the complete explicit target build,
endpoint type locks, all-local-declaration axiom audit, complete audit-log parser,
and fresh replay with the pinned Lean kernel returned actual exit **0**.
The whole suite finished with actual exit **0** at `13:19:08.112199 UTC`, with
source/tool/audit inputs, dependency and binary records, and all recorded
artifacts unchanged across it. The scope and cache use are detailed below.
The earlier [dated partial checkpoint](verification/original-final-target/checkpoint-2026-10-17/README.md)
is retained as historical evidence; its copied running journal is not the final
suite result. Complete original evidence is archived at
[`8ccf3ec0f2d69a7c665a2fb76a6385a1053f6c31`](https://github.com/lixiang90/jsp168-hindman/commit/8ccf3ec0f2d69a7c665a2fb76a6385a1053f6c31)
(E1); the [archive index](https://github.com/lixiang90/jsp168-hindman/blob/8ccf3ec0f2d69a7c665a2fb76a6385a1053f6c31/verification/original-final-target/verified-2026-10-17/archive-index.json) binds original and
stored bytes, including compressed logs. Prize acceptance remains subject to
maintainer review.

**Public release and prize submission — 2026-10-17.** The repository was made
public after the completed verification. Anonymous reads of the selected proof
and evidence index returned HTTP 200 with matching hashes. The formalization
and contribution references were submitted to the official awards catalog in
[PR #5075](https://github.com/TheJustinSunPrize/awards/pull/5075), opened at
`13:58:47 UTC` and awaiting maintainer review. The
[submission record](verification/original-final-target/submission-2026-10-17.json)
preserves the public-access and PR readback results.

This project continues a Lean formalization of **JSP-000168**, corresponding to
[Erdős problem #172](https://www.erdosproblems.com/172). The mathematical source
is OpenAI, [*Monochromatic finite sums and products in the positive integers*,
Theorem 1.1](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Monochromatic-finite-sums-and-products-in-the-positive-integers-September-23-2026/paper.pdf),
September 23, 2026, pinned to OpenAI/math commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
OpenAI receives mathematical solver credit and credit for its upstream formal
proof infrastructure. Local compatibility ports, existing local formalization,
the same-step interval adapter, and final assembly retain their own recorded
provenance. This is an AI-assisted continuation under GitHub account
[@lixiang90](https://github.com/lixiang90); the selected public history must
support every claimed contribution.

## Statement and entry points

The final library target is **`Hindman168.JSP000168`**. The old aggregate
`Hindman168` does not import this final chain, and its default build is not a
substitute for building the explicit target.

The source declaration [`Hindman168.jsp000168_from_openai`](Hindman168/JSP000168.lean)
has the explicit statement:

```lean
∀ (r : ℕ) (χ : ℕ → Fin r) (m : ℕ),
  ∃ (A : Finset ℕ) (c : Fin r),
    A.card = m ∧ (∀ a ∈ A, 0 < a) ∧
      ∀ B : Finset ℕ, B ⊆ A → B.Nonempty →
        χ (∑ b ∈ B, b) = c ∧ χ (∏ b ∈ B, b) = c
```

For every finite coloring and every requested finite size, `A` has exactly
that many distinct positive elements. A single color works for all nonempty
subset sums and products, including singleton subsets. Each member is used
once in a subset expression. The assertion ranges over arbitrary finite sizes;
it supplies no single infinite simultaneous FS/FP sequence. The coloring is
defined on natural numbers, and positive-integer colorings extend at zero.
Positivity of the witness excludes zero from every nonempty sum and product.
The `r = 0` coloring case is vacuous and `m = 0` permits the empty witness.

The stronger source declaration
[`Hindman168.strongConjecture_from_openai`](Hindman168/FinalStrongFromOpenAI.lean)
exposes the paper's full separated conclusion. For every `r`, coloring, `m`,
and **real** `R ≥ 2`, `D ≥ 1`, it produces a strictly increasing positive
sequence `a : Fin m → ℕ` such that, at every index `i`,

```text
R * (sum of a j for j < i + product of a j for j < i)^D < a i
```

where the inequality, sum, product and real power are evaluated in `ℝ`.
The empty preceding sum is zero and product is one, so the first inequality
is `R < a 0`. One color also covers all nonempty indexed subset sums and
products. See the exact definitions in
[`StrongStatement.lean`](Hindman168/StrongStatement.lean).

The final source route is:

1. OpenAI's fixed `exists_native_inverse_on_cyclic_encoding` in
   [`AxisCompression.lean`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AxisCompression.lean).
2. [`OriginalNativeIntervalInverseMenu`](Hindman168/OriginalNativeIntervalInverseMenu.lean)
   and [`OriginalNativeIntervalInverse`](Hindman168/OriginalNativeIntervalInverse.lean):
   same-step interval adaptation, finite native model selection, and
   `native_periodic_interval_inverse_family_from_openai` at order `t ≥ 2`
   and step `t - 1`. Bounds and finite menus are selected before period,
   interval length and bounded input.
3. [`FinalStrongFromOpenAI`](Hindman168/FinalStrongFromOpenAI.lean): the existing
   local deduction receives that inverse family and exports the strong target.
4. [`JSP000168`](Hindman168/JSP000168.lean): the existing indexed-to-finite-set
   conversion preserves positivity, exact cardinality and the one common color.

These canonical source interfaces have compiled in the complete target build.
The selected final verification procedure has also completed successfully at P,
with the exact commands, real exits and input stability recorded below.
Preserved `work-in-progress/` copies can contain the same declaration names;
they must not be imported together with the canonical modules.

## Selected version and actual verification

The selected proof source is `7ae70219fb4034899c6c2d23cc3b58ec6730a1ba` (P). The committed toolchain is
`leanprover/lean4:v4.32.2`, Lean commit
`f3b06c705e6c85f5314019d5d3baab0fec5b580c`; mathlib is pinned to
`905b95818eb32af7874a58b427f50c1711a5e96c`. These are actual recorded checks
at P; **all three checks and the whole suite returned actual exit 0**.

| Evidence | Actual result / pending boundary |
| --- | --- |
| Proof commit P | `7ae70219fb4034899c6c2d23cc3b58ec6730a1ba` |
| Complete explicit target build | Actual Lake exit **0**, bound wrapper exit **0**, **13,720 jobs**; incremental artifacts and pinned official dependency caches were used |
| Build UTC interval | `2026-10-17T11:44:05.740710Z` → `11:58:57.370689Z`; source binding finished `11:59:18.230742Z` |
| Build source/tool binding | Before and after complete JSON snapshots equal byte-for-byte, each SHA256 `9176ef5a4f4d41b796269c88a90e23966ca62b17bef2a68060b12125886b9b7e` |
| Endpoint type locks, suite 01 | Actual exit **0**, `12:03:58.156654Z` → `12:04:57.279741Z`; finite, expanded strong and inverse-family locks compiled; seven key exports inspected |
| All local declarations, suite 02 | Actual exit **0**, `12:04:57.281503Z` → `12:06:11.547739Z`; **5,066 modules**, **70,418 records**, **70,306 unique declaration names** |
| Complete audit-log parser | Actual process exit **0**, summary `passed=true`; exact 5,066 module footers, no missing/extra modules or errors, 95 names shared across modules |
| Observed axiom names | Only `propext`, `Classical.choice`, `Quot.sound` occurred in the complete parsed audit; both final exports printed all three |
| Selected Git raw-byte binding | Actual exit **0**: 5,066 proof sources + 9 repository input files + `.gitattributes` match selected Git blobs/worktree/manifest; no mismatches |
| Static proof-input review | All 5,066 local sources scanned, **145** options classified; no primary or reduction-oracle findings; lexical review only |
| Suite input/artifact stability | 5,076 source/tool/generated-audit inputs passed before and after; 9 dependency pin/status records and 12 toolchain binary hashes were equal; **38,290** artifact files had identical before/after inventories; changed list empty |
| Suite 03, fresh kernel replay | Actual exit **0** for `Hindman168.JSP000168`, `12:06:11.549438Z` → `13:17:44.492924Z` |
| Whole suite / final input comparison | Actual whole exit **0**, `12:02:14.759205Z` → `13:19:08.112199Z`; sources passed, environment records equal, all artifact inventories equal |
| Evidence commit E1 / archived records | `8ccf3ec0f2d69a7c665a2fb76a6385a1053f6c31`; [complete suite result](https://github.com/lixiang90/jsp168-hindman/blob/8ccf3ec0f2d69a7c665a2fb76a6385a1053f6c31/verification/original-final-target/verified-2026-10-17/suite/result.json), [archive index](https://github.com/lixiang90/jsp168-hindman/blob/8ccf3ec0f2d69a7c665a2fb76a6385a1053f6c31/verification/original-final-target/verified-2026-10-17/archive-index.json) |
| Prize review | Maintainer mathematical and Lean review, eligibility and award decisions remain separate from these verification results |

The source inventory SHA256 is `dcf81b5e67766bba2d3bb3f3cc1455e75940a47301e1f79efa9171f96d003796`. The complete manifest SHA256 is `9176ef5a4f4d41b796269c88a90e23966ca62b17bef2a68060b12125886b9b7e`;
the generated all-declaration audit source SHA256 is `eec469be1953dbcebd8ec20a8c5d4981c6427e999579764c287e4eae8e5e8783`. The inventory
contains **2,914 `Hindman168`**, **2,143 `OAI`**, and **9 `PrimeNumberTheoremAnd`**
modules, plus hashes of **9 repository configuration/verification input files**.
Those nine input files are not nine additional proof modules.

[`CheckEndpoint.lean`](verification/original-final-target/CheckEndpoint.lean)
uses `endpointProposition (@theorem)` and `rfl` to compare every binder in the
explicit finite, expanded strong and universe-0 inverse-family statements.
The actual final-export axiom output from suite 01 was:

```text
'Hindman168.strongConjecture_from_openai' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
'Hindman168.jsp000168_from_openai' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

The audit's observed counts were 58,052 records using `Classical.choice`,
62,957 using `Quot.sound`, and 67,414 using `propext`. Individual declarations
may use a subset. The shared names and historical audit totals must not be
added as disjoint declaration counts. The parser binds its complete log to
SHA256 `4cb628013abad789dc2d6c8dafcf56f930efb871b96bde761c0e3a5d0e4d8158`;
the actual parser summary SHA256 is
`c0479b3d93d8386bd9c845bf702e2438afb4801e46e1acf010e9af9ff4628d5c`.

The [complete evidence archive](https://github.com/lixiang90/jsp168-hindman/blob/8ccf3ec0f2d69a7c665a2fb76a6385a1053f6c31/verification/original-final-target/verified-2026-10-17/README.md) preserves actual
[build](https://github.com/lixiang90/jsp168-hindman/blob/8ccf3ec0f2d69a7c665a2fb76a6385a1053f6c31/verification/original-final-target/verified-2026-10-17/build/result.json) and
[suite](https://github.com/lixiang90/jsp168-hindman/blob/8ccf3ec0f2d69a7c665a2fb76a6385a1053f6c31/verification/original-final-target/verified-2026-10-17/suite/result.json) results,
[all-declaration output, gzip](https://github.com/lixiang90/jsp168-hindman/blob/8ccf3ec0f2d69a7c665a2fb76a6385a1053f6c31/verification/original-final-target/verified-2026-10-17/suite/02.log.gz),
[exact scope summary](https://github.com/lixiang90/jsp168-hindman/blob/8ccf3ec0f2d69a7c665a2fb76a6385a1053f6c31/verification/original-final-target/verified-2026-10-17/suite/audit-summary.json),
[fresh replay log, gzip](https://github.com/lixiang90/jsp168-hindman/blob/8ccf3ec0f2d69a7c665a2fb76a6385a1053f6c31/verification/original-final-target/verified-2026-10-17/suite/03.log.gz), and
[actual archival Python parser exit](https://github.com/lixiang90/jsp168-hindman/blob/8ccf3ec0f2d69a7c665a2fb76a6385a1053f6c31/verification/original-final-target/verified-2026-10-17/parser-recheck-execution.json).
Its [index](https://github.com/lixiang90/jsp168-hindman/blob/8ccf3ec0f2d69a7c665a2fb76a6385a1053f6c31/verification/original-final-target/verified-2026-10-17/archive-index.json) records every original/stored
SHA256 and byte length; decompress gzip files before comparing raw log hashes.
Original result text and historical paths are preserved. The archive index SHA256
is `1d8cfa3923c9856a93dba1da2050a18717eacdf4616b4bc342abbefeff5a4a06`.
The earlier [partial checkpoint](verification/original-final-target/checkpoint-2026-10-17/README.md)
retains its fixed running snapshot as history.

The non-`module` audit includes public, private and internal kernel declaration
records in every inventoried local module and checks transitive axiom dependencies,
including those reached through external imports. It does not individually list
unused declarations in external boundary modules. There are 629 unique direct
external import boundaries, not a recursively inventoried external source closure.
The 2,102-module Axis closure and its restored 577-source batch (386 exact upstream
copies / 191 compatibility ports) are narrower scopes; they do not replace the
5,066-module final audit.

The static scanner found no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`/
`extern`/`implemented_by`/`opaque` occurrences in its comment/string-stripped
local scope and no supplemental reduction-oracle findings. It classified 132
resource-limit options, 9 meta-level definitional-equality strategy options,
3 theorem-command aliases and 1 style-linter option. This is a finite lexical
review, not a semantic proof or a replacement for kernel checking.

`leanchecker --fresh` uses **the same pinned Lean kernel**, with an initially
empty checking environment, for safe, nonpartial constants from the target and
imports. Unsafe and partial constants are skipped. It is not an independent
kernel implementation or external mathematical peer review. `--fresh` does not
mean rebuilding Lean, Mathlib or all sources without caches. Its actual final
exit was 0; the complete suite's final source/environment/artifact comparison
also passed. Both artifact-inventory JSON files have SHA256
`5f483070dd08c8fe30c23d49e5e73082c5bb01854d8546b81b950c526988b976`.
The final suite result SHA256 is
`1f8c53c703152cdefe309bb6e3f628c07a675f53e4cd4e9207206b407a852d26`;
03.log SHA256 is
`840e8cb77047623025b36f38543444b66080076eac801b6670ae85dbedc612bd`.

The successful whole build was an incremental `lake -v build
Hindman168.JSP000168`, retaining earlier successful local artifacts and using
pinned official dependency caches. It does not establish a cache-free rebuild
of every dependency. The committed suite does not run or replace that complete
build. The separately recorded complete build and the final three-command suite
are both successful at the selected proof/input checkpoint.

## Reproduce at the selected commit

Install Git, Python 3, and Lean's `elan` toolchain manager. The committed
`lean-toolchain` pins `leanprover/lean4:v4.32.2`; mathlib is pinned to
`905b95818eb32af7874a58b427f50c1711a5e96c`. Keep the complete committed
`lake-manifest.json`; do not run `lake update` as routine setup.
The commands below are the **prepared workflow**, not evidence of an executed
successful reproduction. Choose fresh output directories on repeated runs.

```powershell
git clone https://github.com/lixiang90/jsp168-hindman.git
cd jsp168-hindman
git checkout --detach 7ae70219fb4034899c6c2d23cc3b58ec6730a1ba
lake exe cache get
$env:LEAN_NUM_THREADS = '3'

# Generate an inventory and all-declaration audit without executing Lean.
python verification/original-final-target/prepare.py --output-dir verification-local/release-repro
python verification/original-final-target/static-source-scan.py --manifest verification-local/release-repro/source-closure.json

# Record the complete build's actual exit and full log separately.
lake build Hindman168.JSP000168

# Proceed only after that complete build exits 0.
python verification/original-final-target/run-final-suite.py verification-local/release-repro/source-closure.json release-suite-repro
python verification/original-final-target/summarize-audit.py verification-local/release-repro/source-closure.json verification-local/release-suite-repro/02.log --output verification-local/release-suite-repro/audit-summary.json
```

Stop on any nonzero exit. The suite runs these three commands and records
their actual exits, unmodified logs, and source/artifact/environment hashes:

```powershell
$env:LEAN_NUM_THREADS = '1'
lake env lean -j1 --trust=0 -DautoImplicit=false verification/original-final-target/CheckEndpoint.lean
lake env lean -j1 --trust=0 -DautoImplicit=false verification-local/release-repro/CheckAllDeclarations.lean
lake env leanchecker --fresh --verbose Hindman168.JSP000168
```

The suite output directory is `verification-local/release-suite-repro`.
The parser independently requires every manifest module, declaration record
counts, unique-name counts, a complete footer and only allowed axioms.
Use the parser result together with all three actual suite exits, the separate
complete build exit, and unchanged selected inputs. Record cache usage and
which dependency sources or artifacts were rebuilt. Regenerate the inventory
after any proof or verification-tool change; do not reuse a previous passing
report for changed bytes. See the detailed
[final-target verification instructions](verification/original-final-target/README.md).
The preserved original `verification-manifest.json` and `scripts/verify_snapshot.py`
describe an earlier snapshot; they are useful historical checks and do not
cover the new endpoint by themselves.

## Historical checkpoints and preserved records

The original [`verification-manifest.json`](verification-manifest.json) records
3,059 historical entries. [`scripts/verify_snapshot.py`](scripts/verify_snapshot.py),
[`Hindman168.lean`](Hindman168.lean), and [`Verification.lean`](Verification.lean)
retain that earlier snapshot/default aggregate scope; they do not import the new
final endpoint. Use the explicit target and current inventory for final checks.
Historical partial and conditional results remain useful, with their own dated
assumptions and validation boundaries. The preserved [historical upstream audit](verification/original-upstream-inverse/README.md)
records a 1,525-module coverage union and a 1,469-module recovery audit with
30,068 unique declarations / 30,091 records; 56 modules retained earlier evidence.
Those overlapping totals are historical and must not be added to the new audit.
The conditional `strongConjecture_of_native_inverse` remains an interface;
the new canonical source assembly supplies its inverse-family input.

Original mathematical reviews and attribution records are retained. The removed
3,963 superseded generated logs/results/manifests remain available at the
[pre-cleanup commit](https://github.com/lixiang90/jsp168-hindman/tree/5dc91a1deaf73720b421f672009565e18f4e6dfa).
The 467 removed superseded axiom logs (300,418,280 bytes), and the old scripts'
predecessor paths/hashes, refer to the
[earlier pre-cleanup snapshot](https://github.com/lixiang90/jsp168-hindman/tree/e5e45b1e1227a8df34ee95eadd4b8d87b4811c74).
Restore an old report with `git show COMMIT:PATH` in a separate matching checkout
when replaying that historical checkpoint. Some old scripts need original Windows
paths or predecessor reports. A root README update does not revalidate them.
See the [verification index](verification/README.md) for retained component links.
`work-in-progress/` and scratch files are continuity material and are not all
canonical imports; duplicate declaration copies must not be imported together.

## Credit, provenance and award process

The original mathematical solution is credited to OpenAI. Substantial upstream
OpenAI Lean infrastructure is reused with attribution, exact source provenance
and recorded compatibility diffs. The earlier finite-Szemerédi dependency layer
has its own recorded source pin; do not describe every vendored file as an
unchanged copy of the paper pin. See
[`dependencies/openai-finite-szemeredi/`](dependencies/openai-finite-szemeredi/),
the [historical inverse-source provenance](verification/original-upstream-inverse/README.md),
the [577-source fixed-pin manifest](verification/original-upstream-inverse/prepared-axis-2026-10-17.json),
the [earlier finite-Szemerédi source record](dependencies/openai-finite-szemeredi/SOURCE-MANIFEST.json),
[`PNTPLUS-ATTRIBUTION.txt`](PNTPLUS-ATTRIBUTION.txt), and
[`LICENSE-PNTPLUS`](LICENSE-PNTPLUS). Retain the OpenAI, Mathlib compatibility
and PNT+ license notices. The PNT+ source reference is
`AlexKontorovich/PrimeNumberTheoremAnd` at
`747e480362ef6a0a7341055a84372333d72fa62a`.
No additional blanket license is assigned by this README.

The local contribution continues the existing native-model, uniform Alignment,
same-step linearization and final-deduction development, and assembles the
original cyclic-to-interval inverse route. The earliest retained local commit,
[`eab19c470d9787ca6ad3f0d3bd279ffe6c2aaa0d`](https://github.com/lixiang90/jsp168-hindman/commit/eab19c470d9787ca6ad3f0d3bd279ffe6c2aaa0d),
already preserves substantial local development; the retained history does
not reconstruct its pre-snapshot authorship. Later commits distinguish local
normalization/menu/assembly and compatibility work from imported OpenAI
proofs. Imported recurrence/PET proofs, PNT+ inputs and Mathlib compatibility
sources retain their original attribution and separate source pins.

The continuation and verification tooling are Codex-assisted work maintained
under GitHub `@lixiang90`. Source history supports reviewable contribution
boundaries, not sole human authorship, verified personal identity or priority.
Repository ownership and self-declared Git author metadata alone do not
establish those claims. The [dated contribution/source-history report](verification/original-final-target/checkpoint-2026-10-17/contributions.md) records concrete commit boundaries and its limits; the later one-line adapter closure is in proof commit P. No individual name or
institution beyond the known GitHub account is supplied here.

The mathematical registration [awards #4869](https://github.com/TheJustinSunPrize/awards/pull/4869)
and the related formalization proposal [#4966](https://github.com/TheJustinSunPrize/awards/pull/4966)
must be disclosed. At the dated source check recorded in
[`openai-math-sync-2026-10-17.json`](openai-math-sync-2026-10-17.json), #4869 was
merged and #4966 was open and unmerged; the catalog still recorded Lean proof
and eligibility as No, with independent mathematical review pending. Official
main and #4966 were refreshed again before PR #5075 was opened. Related routes
and claimed contributions require accurate source-level comparison. No first-proof,
priority, award acceptance or payment guarantee is made.

Award acceptance and any payment require the prize's separate review and claim
process. This repository's completed Lean checks do not establish priority,
eligibility, an accepted award or a payment entitlement.
