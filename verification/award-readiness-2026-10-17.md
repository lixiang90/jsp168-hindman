# Award submission readiness — 2026-10-17

This is a source and submission-requirement review, not a completed-proof
certificate. **`Hindman168.StrongConjecture` remains unproved in this repository.**
The current endpoint still takes the all-orders native periodic interval inverse
family as an explicit hypothesis. No prize submission or award claim has been
made for this repository by this review. See the [local target review](target-semantics/README.md)
and [conditional endpoint](../Hindman168/FinalStrongFromNativeInverse.lean).

## Mathematical source and coverage

The fixed source is OpenAI, *Monochromatic finite sums and products in the
positive integers*, September 23, 2026, OpenAI/math commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The
[manuscript metadata](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Monochromatic-finite-sums-and-products-in-the-positive-integers-September-23-2026/README.md)
identifies OpenAI as its author. The
[introduction and Theorem 1.1](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Monochromatic-finite-sums-and-products-in-the-positive-integers-September-23-2026/build/sections/01_introduction.tex#L2-L47)
require arbitrarily large finite sets of distinct positive integers, one common
color for **all** nonempty subset sums and products, and the displayed separation
inequalities for arbitrary real parameters `R ≥ 2` and `D ≥ 1`. Singleton subsets
are included; terms are not repeated within a subset. No infinite simultaneous
sequence is claimed. The local target review explains the checked equivalence
between `FiniteConjecture` and the stronger separated endpoint.

The [current JSP-000168 catalog entry](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0101-0200.md#JSP-000168)
records OpenAI's published complete-solution claim with independent mathematical
review pending, `Lean proof: No`, and `Eligible to claim: No`. Its source registration
was merged as [awards PR #4869](https://github.com/TheJustinSunPrize/awards/pull/4869).
This problem is absent from the [49-problem MathDB pilot register](https://github.com/TheJustinSunPrize/awards/blob/main/problems/mathdb-pilot.md),
so the repository's legacy submission process applies at the time of this review.
These are mutable upstream records and must be checked again before submission.

## Existing complete-formalization submission

[Awards PR #4966](https://github.com/TheJustinSunPrize/awards/pull/4966), by
`cadamcat`, is open and unmerged as checked on 2026-10-17. Its selected proof is
[cadamcat/hindman-sums-products-lean4 at `5d18600a4518d42d5b1e916e908e50330eb38456`](https://github.com/cadamcat/hindman-sums-products-lean4/tree/5d18600a4518d42d5b1e916e908e50330eb38456),
with target `HindmanSumsProducts.hindman_finite_sums_products`. The PR reports
author-run build, axiom and kernel checks; this review has not reproduced them
or established acceptance by the prize maintainers.

That project has an [Apache-2.0 LICENSE](https://github.com/cadamcat/hindman-sums-products-lean4/blob/5d18600a4518d42d5b1e916e908e50330eb38456/LICENSE),
[Yao Xu copyright NOTICE](https://github.com/cadamcat/hindman-sums-products-lean4/blob/5d18600a4518d42d5b1e916e908e50330eb38456/NOTICE)
and [third-party attribution record](https://github.com/cadamcat/hindman-sums-products-lean4/blob/5d18600a4518d42d5b1e916e908e50330eb38456/THIRD_PARTY.md).
Its [toolchain](https://github.com/cadamcat/hindman-sums-products-lean4/blob/5d18600a4518d42d5b1e916e908e50330eb38456/lean-toolchain)
is Lean 4.34.1. Its [manifest](https://github.com/cadamcat/hindman-sums-products-lean4/blob/5d18600a4518d42d5b1e916e908e50330eb38456/lake-manifest.json)
pins mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` and OpenAI/math
`adc7f1241b42e322a6451854ab7e4b4c146bf78a` (`lean/`), alongside its other dependencies.
This does not change this repository's pinned toolchain or dependencies.

The mathematical interfaces differ materially. Its
[`InverseBridge.cyclic_inverse_menu`](https://github.com/cadamcat/hindman-sums-products-lean4/blob/5d18600a4518d42d5b1e916e908e50330eb38456/HindmanSumsProducts/InverseBridge.lean)
produces linear models of step `2 * (t - 1)`. Its
[`Prediction/Subgroup.lean`](https://github.com/cadamcat/hindman-sums-products-lean4/blob/5d18600a4518d42d5b1e916e908e50330eb38456/HindmanSumsProducts/Prediction/Subgroup.lean#L7-L22)
explicitly replaces the paper's concatenation bound and deletes the cyclic-to-interval
periodization route. Those results do not directly establish this repository's
same-step input `HasNativePeriodicIntervalInverse (t - 1) t`.

The relevant original inverse endpoint is
[`OAI.Erdos3.exists_cyclicNativeInverse_positive`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AxisCompression.lean#L292).
The same file's
[`exists_native_inverse_on_cyclic_encoding`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AxisCompression.lean#L318)
supplies a same-step `NativeSampleCorrelation` under finite-support norm,
density and pair-sum-reflecting encoding hypotheses. A local adapter must prove
these hypotheses, the finite model selection and the interval correlation; the
existence of the upstream declaration alone does not discharge the local target.

## Requirements before any submission

The [contribution requirements](https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md#external-solver-and-lean-submissions)
accept complete solutions to the original problem. Partial, conditional or
placeholder-dependent proofs do not qualify. A Lean submission must link the
complete mathematical solution and distinguish its solver from the formalization
contributors. Submit references and catalog text to awards; proof sources,
dependencies and build artifacts stay in the external proof repository. External
submissions edit the relevant catalog's permitted status, Lean proof, attribution
and publication fields; maintainers reconcile eligibility and the index.

The [PR template](https://github.com/TheJustinSunPrize/awards/blob/main/.github/PULL_REQUEST_TEMPLATE.md)
requires, for a Lean submission:

- JSP ID, exact original source, proposed catalog change and relevant related PRs;
- complete solution and its mathematical review status;
- pinned formal statement and proof locations, fully qualified target name and
  coverage of definitions, assumptions, quantifiers and required cases;
- original proof repository, named branch and full 40-character commit SHA
  contained in that branch;
- exact toolchain, dependency pins, setup/build/target-check commands and the
  target's complete axiom report;
- authorship and contribution evidence, with co-contributors distinguished.

Self-check reports are optional supporting evidence. The
[verification guide](https://github.com/TheJustinSunPrize/awards/blob/main/docs/verification.md)
requires an accurate description of the version and verification levels actually
checked; a successful mechanical audit does not establish original-problem
correspondence or remove an explicit hypothesis.

Under the [legacy award process](https://github.com/TheJustinSunPrize/awards/blob/main/docs/award-process.md#lean-formalization-or-both-roles),
mathematical review precedes Lean acceptance. Priority compares verified selected
complete-proof versions and independently checkable public history, not PR opening
times or commit timestamps alone. A pending PR does not satisfy the merged-PR
requirement for a Lean award claim. Candidate publication starts a separate
14-day public review; identity verification and written recipient confirmation
remain later requirements. The existing #4966 must be disclosed and any claimed
difference supported. No first-proof, priority, acceptance or payment conclusion
is established here.

The [attribution rules](https://github.com/TheJustinSunPrize/awards/blob/main/docs/attribution.md#lean-contributor-verification)
require the applicant's actual contribution in its original repository; uploading
or owning a copy of another person's proof does not establish authorship. Any
external result reused here must retain its source, license and contributor
attribution, and any application must describe the actual local contribution.

**Readiness: incomplete.** Finish the unconditional target, verify its exact
committed version, retain accurate attribution, and recheck the upstream records
before publishing a complete-proof submission.
