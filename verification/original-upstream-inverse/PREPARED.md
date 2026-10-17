# Prepared continuation, 2026-10-17

The verified checkpoint remains the one in `current-replay.json` and README.
This continuation does not extend its compiled or audited coverage.

`prepared-frontier-2026-10-17.json` records 23 additional source modules from
OpenAI/math commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`: 17 exact copies
and 6 API compatibility ports with file-level notices and complete diffs.
Original Git blob identities and source SHA-256 hashes were recomputed.
Their complete local OAI source import closure has no missing files. These
checks establish source identity and availability, not successful Lean builds.

`prepared-axis-2026-10-17.json` extends preparation to all 577 missing modules:
386 exact sources and 191 compatibility ports. The actual 2,102-module Axis
import closure is recorded in `axis-prepared-modules.txt`; it is acyclic and
has no missing OAI source imports. All corresponding Mathlib source imports
exist at the fixed dependency revision. Local original files were used to
recompute each original Git blob, both SHA-256 hashes, and the full port diff.
These are still source checks: the complete Axis endpoint has not compiled.
Direct strict source checks against existing dependency artifacts are recorded
in the prepared manifests, including `UnitVerticalMeanRowCorrelation`,
`ComparisonProductMetric`, and `CommonNativeSquareFactors`. Their latest changes
make finite-sum comparisons, definitional equalities, and translation evaluation
explicit. `AllocatedMarkedDictionaryRecovery` makes canonical realification and
existing product-topology instances explicit, and types the same original metric
before its use; its complete file also passed a strict direct source check.
These changes retain the original mathematical hypotheses.
Direct strict source checks also passed for `BoundedRootDegreeEquivalence`,
`PositiveShiftTestingGowers`, `PrescribedPartitionExpansionCore`, and
`MixedFrozenMiddleRows`. Their latest changes make dependent equality transport,
empty-index seminorm evaluation, the definitionally equal `none` factor, and
finite corner-cardinality evaluation explicit, retaining the original
mathematical hypotheses and model structures.
The latest budget repairs to `UniformControlledCurrentStage`,
`NativeCoordinateDerivativeSystem`, `NativeFormalPolynomialSystems`,
`ExtractedInitialState`, `FastKernelReabsorptionControl`,
`PositiveShiftRefilteredExpansion`, `UnnormalizedCommonSymbolFactorization`,
`MarkedEvaluationJointBounds`, and `CommonMarkedDirectionCoordinates`
add only finite declaration-local `maxHeartbeats 1000000` after actual
default-budget timeouts. Their mathematical statements and existing proof
bodies are unchanged by these budget adjustments.
The prepared-source verifier permits those exact options only once in each
recorded module, immediately before its corresponding theorem.
Those single-module exits do not extend the complete Axis build or axiom audit.

Read-only reproduction of the committed prepared source inventory:

    python verification/original-upstream-inverse/verify-prepared.py --manifest verification/original-upstream-inverse/prepared-axis-2026-10-17.json

Exact copies can be verified from their current bytes. Without separately
retrieved fixed originals, this portable command explicitly reports that
modified originals and their diffs were not freshly replayed. Supplying
`--raw-root` with fixed originals enables that additional local comparison.

`Hindman168.OriginalNativeIntervalInverseMenu` isolates a conditional bridge
from uniformly bounded rational niltests to the exact same-step native
periodic interval interface. The uncompiled draft
`work-in-progress/OriginalNativeIntervalAdapter.lean` supplies its input using
the fixed upstream `exists_native_inverse_on_cyclic_encoding`; the separate
`OriginalStrongFromOpenAI.lean` draft assembles the existing final deduction.
`JSP000168Statement.lean` also displays the explicit positive, exact-cardinality
finite sums/products statement using only standard finite-set vocabulary.
The drafts preserve the degree, norm normalization and pre-input finite-menu
quantifiers. They contain no placeholder proofs, but they have not yet passed
Lean compilation or axiom checks. They are outside the canonical build.

The same prepared proof chain is now available as properly named library
modules `OriginalNativeIntervalInverse`, `FinalStrongFromOpenAI`, and
`JSP000168`. The current complete source-build target is:

    lake build Hindman168.JSP000168

The full target build and audit are still pending; see the separate
[final-target verification status](../original-final-target/README.md).
Their names alone do not establish a theorem. They must not be imported together
with the WIP copies, which intentionally retain their earlier prepared declarations.

The main theorem is still unproved in the verified repository. No publication
or prize submission milestone is established by this prepared continuation.
The original snapshot and current replay manifests are unchanged.

All fixed dependency revisions and matching dependency caches have been recovered
locally without changing the lockfile; the complete source build is in progress.
See [the award readiness review](../award-readiness-2026-10-17.md)
for current submission requirements and related pending work.
