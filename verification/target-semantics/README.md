# Hindman target and alignment semantic review

Date: 2026-10-14 UTC. Review is read-only with respect to the repository source, canonical aggregate, Verification.lean, and frozen manifest. All new checks and this report are outside the repository.

## Result

No target-weakening, wrong quantifier order, wrong raw law, subset restriction, strictness loss, or empty-type shortcut was found in the reviewed final assembly.

The checked final mathematical statement is still CONDITIONAL:

    (∀ t : ℕ, 2 ≤ t → HasNativePeriodicIntervalInverse.{u} (t - 1) t)
      → StrongConjecture

The inverse family has not been supplied by this review. Neither the formalization of the entire paper nor an unconditional proof of Theorem 1.1 is certified here. A build and a standard-axiom report do not remove a theorem's explicit hypothesis.

StrongConjecture is equivalent to the positive-integer, positive-color-count, positive-size statement of Theorem 1.1 after ordinary finite-index relabeling. Independent external Lean proofs check the natural-number-domain and first-index normalizations. FiniteConjecture is not literally the paper statement: its direct definition permits 0 and asks for cardinality at least m. The repository's independently checked finite_iff_strong proves the required equivalence, so that difference does not weaken the delivered Strong endpoint.

## Fixed references and verification scope

- Paper: OpenAI, “Monochromatic finite sums and products in the positive integers”, September 23, 2026, Theorem 1.1, Definition 2.1–2.2, Principles 2.3–2.4, and the interval inverse statement in §5.3.
- Requested upstream reference: OpenAI/math, adc7f1241b42e322a6451854ab7e4b4c146bf78a.
- Reviewed final private checkpoint: b33c29f88ed0770afc52dc3b5cf8695198e23b5d, confirmed by the integrator after the uniform-alignment commit. Remote commit identity is integrator-provided; this reviewer independently read the local files and checked their hashes.
- Local paper PDF SHA-256: ab835f6a98c10d6d4498b19e7446facd7b481fef85fee54232c76b45bc9e0888.
- Local paper text SHA-256: 47e3c31d5a16aca446a3b5003bcf3d18e1feed114b569dc41299dee0ada9d2f0.
- All 10 hashes in verification/uniform-alignment/source-sha256.txt matched the reviewed source.
- Independently ran scripts/verify_snapshot.py: all original 3059 source hashes matched; its unchanged status is Full target proved: False.
- Independently ran two external Lean files using Lean 4.32.2, lake env lean --trust=0, one Lean thread. Both final runs exited 0. These are import-based targeted semantic checks, not this reviewer's rebuild of all imported source modules.
- The integrator separately reports a 6929-job build and a 150-declaration standard-three-axiom audit for the uniform-alignment batch. That is distinguished from the checks directly performed here.

## 1. Exact target statement

### 1.1 StrongConjecture and Theorem 1.1

Hindman168/StrongStatement.lean:19–29 defines StrongWitness and StrongConjecture.

The fields are:

1. a : Fin m → ℕ;
2. StrictMono a, hence all m entries are distinct and increasingly ordered;
3. ∀ i, 0 < a i;
4. for every i, the strict real inequality
   R * (sum of all a j with j < i + product of all a j with j < i)^D < a i;
5. one color c : Fin r before the universal quantifier over every nonempty S : Finset (Fin m);
6. both χ(sum over S) = c and χ(product over S) = c.

R and D are arbitrary REALS, with 2 ≤ R and 1 ≤ D. No conversion to integral exponents or weakening from < to ≤ occurs. Fin m is merely the zero-based relabeling of the paper's [m]. Each subset is a Finset, so an index occurs at most once. There is no restriction to intervals, initial segments, pair sums, a preselected family of subsets, or subsets of a prescribed cardinality. Singleton subsets are included.

At i=0 the filtered predecessor set is empty. Its sum is 0 and product is 1, so the displayed field is exactly R < a 0, for every real D. At later i it is exactly equation (1.1).

External checked theorem strongWitness_iff_paperSplit proves equivalence with the explicit first-term inequality and the later-index inequalities, rather than relying only on a prose interpretation of empty sums/products.

The paper colors positive integers, whereas the repository colors all naturals. External checked theorem strong_iff_paper_positive proves a two-way equivalence with a proposition quantified only over r,m>0 and colorings of {n : ℕ // 0 < n}. The forward direction extends the coloring to 0 using the color of 1; every resulting sum and product is proved positive. The reverse direction restricts a natural-number coloring to positive inputs and separately supplies the m=0 case. The finite color labels 0,…,r−1 and 1,…,r are interchangeable labels; their numerical values are never used in the conclusion.

### 1.2 FiniteConjecture is an equivalent interface, not a literal transcription

Hindman168/Basic.lean:23–30 defines MonoFSFP and FiniteConjecture. The direct definition asks for A : Finset ℕ with m ≤ A.card; it does not itself require all members positive or exact cardinality m, and it contains no R,D separation parameters.

The bridge is substantive and present:

- StrongStatement.lean:31–41: strong_to_indexed and strong_implies_finite.
- Basic.lean:71–104: indexed_to_finset, exact cardinality m and positivity, using injectivity to preserve sums and products under image.
- FiniteToStrong.lean:17–84: refine the coloring, delete [0,T], and enumerate a size-m subset increasingly.
- QuantitativeSeparation.lean:77–112: a finite log-log coloring forces pairwise power separation from monochromatic products.
- FiniteToStrong.lean:88–166: the pairwise real-power gaps imply the precise sum-plus-product inequality.
- FiniteToStrong.lean:170–195: finite_implies_strong and finite_iff_strong.

I read the separation proof, not merely its name. The auxiliary color distinguishes b from ab when a≤b≤a^E; the monochromatic finite-products property forces a^E<b. Deleting at most T+1 elements leaves the requested cardinality. The final exponent is mD+1, and the coefficient bound uses R(m+1)^D. The proof handles the first index separately and retains strict inequalities.

It is therefore accurate to say that the finite endpoint suffices for the paper's theorem through the checked bridge, but inaccurate to describe Basic.FiniteConjecture's literal definition as already containing all of Theorem 1.1.

## 2. Final endpoint parameters and unclosed dependency

Hindman168/FinalStrongFromNativeInverse.lean:10–18 contains:

- finiteConjecture_of_native_inverse.{u};
- strongConjecture_of_native_inverse.{u}.

The independent @-checks with pp.explicit and pp.universes confirm exactly one theorem hypothesis: the displayed all-orders native inverse family. There is only a universe level besides it. There is no hidden section variable, typeclass oracle for alignment, requested-witness premise, parameter-family existence premise, positive-count premise, or model existence premise on either final theorem.

Hindman168/FinalUniformAlignment.lean:12 gives hasUniformSelectedPrincipalAlignment.{u} with no theorem hypotheses.

Hindman168/NativePeriodicIntervalInverseThreshold.lean:13–25 expands the remaining inverse input as follows:

- for every real δ>0;
- choose a nonempty finite list of native nilmanifold data of step at most s, Lipschitz bounds, and γ>0;
- these choices precede q, its NeZero instance, K, and the real unit-bounded function v : ZMod q → ℝ;
- if the normalized interval Gowers value of v on [0,Kq) is at least δ/4;
- produce an index, a unit-bounded Lipschitz complex observation, and group elements g,x with correlation at least γ.

The final input sets s=t−1 and d=t for every t≥2. Natural subtraction cannot change that step relationship because t≥2 is explicit. NativeNilmanifoldData includes finite-dimensional Lie data, connectedness, simple connectedness, nilpotence and the step bound, a discrete lattice, compact quotient, and a metric compatible with the quotient topology (NativeNilmanifoldData.lean:14–41).

This is an explicitly needed periodic-real-input specialization of the cited integer-interval inverse theorem, not a completed proof of the full GTZ result. In particular, a future adapter must actually produce this finite-list native data and its quantifier order; merely compiling a port of an upstream inverse theorem does not instantiate this argument. The repository accepts a compatible quotient metric; identification with particular smooth-metric formulations is part of the adapter justification, not a fact certified by this target review.

FinalNativeInverseStep.lean:25–47 proves that one finite step bound suffices for every row order needed by prediction. The d=0 row case asks for U¹, which is supplied by native_periodic_interval_inverse_one, a genuine theorem using a trivial nilmanifold and the mean identity (NativePeriodicIntervalInverseOne.lean:19–34). Higher-order cases use the explicit hinverse. The remaining all-orders input is not discharged by these first-order and monotonicity lemmas.

Independent #print axioms checks on both final endpoints, hasUniformSelectedPrincipalAlignment, finite_iff_strong, maskGeneratedMaster_conditions, finite_scale_prediction_models_unit_observables, principal_final_deduction_tolerances, and principal_positive_sum_yields_finite_witness return only propext, Classical.choice, and Quot.sound. This rules out new axioms in those dependency closures; it does not erase the explicit inverse hypothesis.

## 3. Uniform alignment quantifier order and actual use

FinalUniformAlignmentInput.lean:13–30 has the order:

    ∀ n r s,
    ∃ B A hclosed, B.Nonempty ∧ positive B ∧ positive A ∧
    ∃ δ>0,
    ∀ d M hM P F, MasterParameterConditions M A P F →
    ∀ e, e is in range M →
    ∀ S, all S are NativePieceRepresented s at the selected gaps →
         all values lie in [0,1] →
    ∀ θ>0, δ ≤ liminf_w original_raw_mass(alignment_event).

B, A, their closure proof, and δ precede parameters, selected indices, model functions, model manifolds, model Lipschitz bounds, and θ. No model complexity appears before δ. The quantifiers match the required tolerance-first deduction.

The proven data in SelectedAlignmentScheduleFinal.lean:93–112 are concrete functions of n,r,s:

- B = selectedAlignmentScheduleFinal n r s;
- A = selectedAlignmentScheduleScales n r s;
- δ = selectedAlignmentScheduleDelta n r s.

SelectedAlignmentScheduleIndexed.lean:66–92 gives strictly positive finite route counts and

    δ = product over i<n of 1 / (3 * Q_i * Q_i).

These route counts derive from the finite schedule alone. The dependency order does not loop back through the models or thresholds. FinalUniformAlignment.lean:16–27 only identifies the masterGapIndex function with the selected actual gap; its unused unit-range hypothesis means that the intermediate alignment theorem is stronger, not that model bounds are absent from the counting deduction.

This is a selected-master-family formulation. It should not be advertised as a separately proved equivalence with every abstract family satisfying only paper Definition 2.1. That broader equivalence is unnecessary for the main endpoint because the final proof constructs the required master family and its conditions.

FinalStrongFromPrinciples.lean:18–44 actually follows the required order:

1. derive s from the inverse family and choose n by product-chain selection;
2. choose B,A,δ from alignment;
3. choose positive θ,η from the finite data and δ;
4. construct prediction models and their sufficiently large master count;
5. take M=N+1 and construct maskGeneratedMaster with its proved conditions;
6. choose a cofinal ultrafilter and obtain e, models, representedness and prediction limits;
7. apply the already chosen alignment data to those exact models and θ;
8. feed that exact event liminf into principal_final_deduction_tolerances;
9. obtain an actual positive finite set of cardinality m+1, hence at least m;
10. use finite_implies_strong for the full separated result.

No selected parameter or model is assumed to exist without a producing theorem. maskGeneratedMaster_conditions (MaskGeneratedOriginalTemplates.lean:61–65) supplies the hF actually consumed; FiniteScaleNativeUnitModels.lean:35–50 supplies the e, heM, same represented model functions and their [0,1] bounds. Its conclusion also supplies common-quotient, uniformly bounded global observations (lines 193–202), so the final consumer is not relying on per-piece unbounded-complexity witnesses.

## 4. Exact event, arbitrary subsets, and original raw measure

### 4.1 Event

PositivePrincipalSumEvents.lean:33–39 defines:

    ∃ b : B, ∀ κ : Fin r, PrincipalAddingAlignment ...

Thus one b works simultaneously for all colors. b is not chosen after the color, block, or subset.

PositivePrincipalSumAlignment.lean:20–31 then universally quantifies:

- every nonempty tail T and pivot i with all tail entries < i;
- every Finset D of AlignmentAddingPair n i with targetTail=T;
- the implication from strict center threshold 2θ<S to strict shifted threshold θ<S.

AlignmentAddingPairs.lean:10–18 is precisely the ordering ∅≠P<T<j<i in paper equation (2.1). It does not omit eligible earlier blocks or require that D be a chain. Empty D is allowed. Finset membership prevents repeated additions. The source block is sourceTail∪{sourcePivot}, and its ordered decomposition is unique, so pair indexing does not manufacture duplicate copies of a source block.

FiniteScaleClosure (FiniteScaleLists.lean:12–13) includes every nonempty subset product, in fact more than merely the paper's nonsingleton blocks. ScaleColorIndex is A×Fin r, and scaleBlockColorIndex carries the actual product-membership proof. There is no arbitrary replacement scale.

The event uses natural-number coefficient division, which would be dangerous without eventual integrality. PositivePrincipalSumRatios.lean:44–95 proves simultaneously that the source and target coefficients are positive, the target divides the source, and the natural quotient equals exactly (h_A b_A)/(h_B b_B). Thus no rounding remains at the sufficiently late stages used by the liminf. The threshold-to-event adapter consumes that exact equality.

### 4.2 Raw law and adapter

SelectedPrincipalRawLaw.lean:22–24 defines selectedPrincipalRawMass as the independent product of the original rawMass at the selected principal cutoffs and primorial(w).

HarmonicSampling.lean:17–24 and HarmonicMass.lean:104–109 identify rawMass with

    1_[X,X²)(y) * 1_coprime(y,W) * (1/y) / Z.

It is not a replacement Haar measure, uniform interval measure, conditioned success law, or arbitrary auxiliary measure. SelectedPrincipalRawLaw.lean:26–36 proves exact eventual pushforward equality from the full original raw product law, and lines 52–63 prove nonnegativity and total mass one eventually. PositivePrincipalSumEvents.lean:42–52 proves positive support coordinates.

The actual new proof chain is:

- selected_alignment_schedule_native_path_liminf;
- selected_alignment_schedule_native_liminf;
- principal_native_threshold_liminf_le_alignment;
- selected_alignment_schedule_alignment_liminf;
- selected_alignment_finite_data_mass;
- hasUniformSelectedPrincipalAlignment.

The middle adapter is PositivePrincipalSumFutureEvent.lean, not merely the older palette-request theorem. It derives the concrete selected event from the simultaneous actual 2θ-to-θ threshold requests, uses the exact original raw pushforward, and applies event monotonicity only on supported samples. Liminf comparison includes the required eventual boundedness hypotheses. Consequently the event and measure returned at the endpoint are exactly the event and measure accepted at PositivePrincipalSumFinalDeduction.lean:39–40.

The final deduction uses δ/2 along the same cofinal ultrafilter via PositivePrincipalSumTolerances.lean:45–56. Calibration, positive numerical budget, and model-count comparison then yield positive actual weighted counts. PrincipalCountWitness.lean:90–165 extracts real supported coordinates and proves an injective positive witness; it does not infer a witness merely from a model-count label.

## 5. Empty and boundary cases

The following were checked in external Lean examples as well as by reading the consumers:

- r=0: any supposed χ : ℕ→Fin r already implies 0<r by χ 0. Universal statements at r=0 are vacuous only because no coloring exists; this cannot discharge any r≥1 instance.
- m=0: StrongWitness has the unique empty sequence, vacuous positional fields, and an actual color χ 0. This is a harmless extension beyond the paper's m≥1 scope.
- n=0: alignment has no blocks. B remains nonempty, so its event is the full sample space; the empty-schedule δ is exactly 1. There is no zero-mass trick.
- A empty: if n>0 and B is nonempty, FiniteScaleClosure applied to a singleton forces A.Nonempty. This was checked directly.
- Nonempty output chain: PrincipalCoordinateChain n (m+1) implies n≥2, using a nonempty tail below its first pivot. The actual positive-size deduction cannot use an empty chain type as its witness.
- M=0: the final interface requires hM:0<M, and the assembly sets M=N+1.
- d=0 in the row-order family gives inverse order 1, which is proved separately. It does not call the higher-order premise outside its range.
- q=0 in the remaining inverse is excluded by NeZero q.
- K=0: the interval cube domain is empty and integerIntervalPeriodicGowersValue q d 0 v=0. This equality was checked directly, so δ>0 makes the positive-threshold premise false. No division by a zero interval size yields a spurious inverse witness.
- θ>0 is unrestricted in alignment, but final tolerances satisfy θ<1/4. An all-zero model may make the bare alignment implication vacuous; it cannot by itself satisfy the calibration/count conditions and positive numerical budget used to obtain the final witness.

## 6. External artifacts and reproduction

Directory: /workspace/shared/hindman-target-semantic-audit/

1. EndpointChecks.lean and EndpointChecks.log
   - complete explicit endpoint signatures and expanded definitions;
   - standard-axiom checks for the final dependency endpoints;
   - strongWitness_iff_paperSplit;
   - singleton, r=0, m=0, n=0, scale-nonemptiness, chain-nonemptiness, and K=0 checks.
2. PaperDomainChecks.lean and PaperDomainChecks.log
   - PaperPositiveConjecture;
   - strong_to_positive_domain;
   - positive_domain_to_strong;
   - strong_iff_paper_positive.
3. FrozenSnapshot.log, ReviewedSourceSha256.txt, and sha256.txt.

Current check-source SHA-256 values:

- EndpointChecks.lean: b1c21e0c0dd30cb6f0b647ac05c5783a6fe98e5234b0bddc2415c7ae6f0e3894
- PaperDomainChecks.lean: d3fe9fa3f28db7597ec5b2be3049b4462f67a33765683749635f46ce7c8e4e0e

From /workspace/shared/jsp168-hindman, with the existing toolchain:

    ELAN_HOME=/workspace/shared/hindman-tools/elan
    PATH=$ELAN_HOME/bin:$PATH
    LEAN_NUM_THREADS=1
    lake env lean --trust=0 /workspace/shared/hindman-target-semantic-audit/EndpointChecks.lean
    lake env lean --trust=0 /workspace/shared/hindman-target-semantic-audit/PaperDomainChecks.lean
    python scripts/verify_snapshot.py

No proof source was changed, no canonical verification list or manifest was rewritten, and no publication or prize action was taken by this reviewer.

## Completion criterion still outstanding

The next required mathematical artifact is an unconditional proof of the exact family

    ∀ t : ℕ, 2 ≤ t → HasNativePeriodicIntervalInverse.{u} (t - 1) t

at a suitable universe, with its finite-list, step, metric, normalized-interval, unit-bound and correlation obligations all discharged. Then the existing conditional endpoint must be applied to that artifact and the resulting unconditional StrongConjecture declaration checked and audited. The current native-inverse port under construction is outside this fixed review snapshot. Until this happens, the correct status remains: target semantics and the alignment-to-final interface checked; full theorem not yet unconditionally proved.
