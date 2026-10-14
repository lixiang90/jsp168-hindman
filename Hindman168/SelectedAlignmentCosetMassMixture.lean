import Hindman168.SelectedAlignmentCosetMassCover
import Hindman168.NativeOriginalPointWeakLimit

namespace Hindman168
open MeasureTheory Module Filter Set
open scoped Topology Manifold ContDiff BigOperators ENNReal NNReal Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_layer_haar_initial_eq {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (H : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ) (h : D.G) :
    letI : MeasurableSpace D.G := borel D.G
    nativeRationalLayerHaarImage D H 0 ρ hρ h = nativeRationalLayerHaarImage D H 1 ρ hρ h := by
  letI : MeasurableSpace D.G := borel D.G
  have he : nativeRationalSubgroupLayerAlgebra D H 0 = nativeRationalSubgroupLayerAlgebra D H 1 := by
    apply LieSubalgebra.toSubmodule_injective
    exact H.initial
  unfold nativeRationalLayerHaarImage nativeRationalLayerOrbitMap nativeRationalLayerOrbitData
    nativeRationalSubgroupLayer
  let make (L : {L : LieSubalgebra ℝ (GroupLieAlgebra D.I D.G) //
      nativeLatticeRationalSubspace (E := D.E) (I := D.I) D.Γ L.toSubmodule}) :
      Measure (D.G ⧸ D.Γ) := by
    let A := roughNativeSubgroupNilmanifold D L.val L.property
      (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) ρ)
      ((nativeSubgroupRationalHull_mem_iff (E := D.E) (I := D.I) D.Γ ρ).mp hρ)
    letI : MeasurableSpace A.E := borel A.E
    letI : MeasurableSpace A.G := borel A.G
    let T : A.G ⧸ A.Γ → D.G ⧸ D.Γ :=
      roughConjugateOrbitMap D.Γ (nativeLieSubalgebraSubgroup L.val)
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) ρ)) h
    exact Measure.map T (nativeNilmanifoldQuotientProbability A)
  exact congrArg make (show (⟨nativeRationalSubgroupLayerAlgebra D H 0,H.rational 0⟩ :
    {L : LieSubalgebra ℝ (GroupLieAlgebra D.I D.G) //
      nativeLatticeRationalSubspace (E := D.E) (I := D.I) D.Γ L.toSubmodule}) =
      ⟨nativeRationalSubgroupLayerAlgebra D H 1,H.rational 1⟩ from Subtype.ext he)

/-- Integrate a fixed measurable set along the original unit-interval curve.
The H₀/H₁ equality is proved from the filtration, not postulated. -/
theorem native_rational_curve_haar_mass_ge {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (H : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : ℝ → D.G) (hh : Continuous h) :
    letI : MeasurableSpace D.G := borel D.G
    ∀ (E : Set (D.G ⧸ D.Γ)) (hE : MeasurableSet E) (δ : ℝ≥0∞),
      (∀ β : ℝ, δ ≤ nativeRationalLayerHaarImage D H 1 ρ hρ (h β) E) →
      δ ≤ nativeRationalCurveHaarImage D H 0 ρ hρ h E := by
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_coset_borel D
  let A := nativeRationalLayerOrbitData D H 0 ρ hρ
  letI : MeasurableSpace A.E := borel A.E
  letI : MeasurableSpace A.G := borel A.G
  letI := A.metric
  letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (A.G ⧸ A.Γ) := native_nilmanifold_metric_coset_borel A
  letI := unit_interval_probability_isProbability
  letI := native_nilmanifold_quotient_probability_isProbability A
  intro E hE δ hbound
  let T : ℝ × (A.G ⧸ A.Γ) → D.G ⧸ D.Γ :=
    fun z => nativeRationalLayerOrbitMap D H 0 ρ hρ (h z.1) z.2
  have hT : Continuous T := (native_rational_layer_orbit_metric_joint_continuous D H 0 ρ hρ).comp
    ((hh.comp continuous_fst).prodMk continuous_snd)
  change δ ≤ (Measure.map T (unitIntervalProbability.prod (nativeNilmanifoldQuotientProbability A))) E
  rw [Measure.map_apply hT.measurable hE, Measure.prod_apply (hT.measurable hE)]
  calc
    δ = ∫⁻ _ : ℝ, δ ∂unitIntervalProbability := by simp
    _ ≤ _ := by
      apply lintegral_mono
      intro β
      have hb := hbound β
      rw [← native_rational_layer_haar_initial_eq D H ρ hρ (h β)] at hb
      have hc : Measurable (nativeRationalLayerOrbitMap D H 0 ρ hρ (h β)) :=
        ((native_rational_layer_orbit_metric_joint_continuous D H 0 ρ hρ).comp
          (continuous_const.prodMk continuous_id)).measurable
      rw [nativeRationalLayerHaarImage, Measure.map_apply hc hE] at hb
      convert hb using 1
      rfl

/-- Actual finite-residue / interval mixture mass, with no measurable
choice of lifts: only the one fixed measurable set E is integrated. -/
theorem native_point_mixture_mass_ge {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (H : NativeRationalSubgroupFiltration D ℓ)
    (M : ℕ) (hM : 0 < M) (sigma : Fin M → D.G)
    (hRat : ∀ r, sigma r ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : ℝ → D.G) (hh : Continuous h) :
    letI : MeasurableSpace D.G := borel D.G
    ∀ (E : Set (D.G ⧸ D.Γ)) (hE : MeasurableSet E) (δ : ℝ≥0∞),
      (∀ (r : Fin M) (β : ℝ), δ ≤ nativeRationalLayerHaarImage D H 1 (sigma r) (hRat r) (h β) E) →
      δ ≤ (nativePointMixtureProbability D H M hM sigma hRat h hh : Measure (D.G ⧸ D.Γ)) E := by
  letI : MeasurableSpace D.G := borel D.G
  intro E hE δ hbound
  have hb (r : Fin M) := native_rational_curve_haar_mass_ge D H (sigma r) (hRat r) h hh E hE δ (hbound r)
  change δ ≤ (finiteProbabilityMixture (fun r => nativeRationalCurveHaarImage D H 0 (sigma r) (hRat r) h)) E
  simp only [finiteProbabilityMixture, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul, Fintype.card_fin]
  calc
    δ = (M : ℝ≥0∞)⁻¹ * ((M : ℝ≥0∞) * δ) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hM.ne') (by simp), one_mul]
    _ ≤ _ := mul_le_mul_left' (by simpa using (Finset.sum_le_sum (s := Finset.univ) (fun r _ => hb r))) _
theorem selected_alignment_mixture_closed_union_mass
    {ι κ : Type} [Fintype ι] [Finite κ] {n M : ℕ} (f : Fin n ↪o Fin M) (i : Fin n) {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) (r : ι → ℕ)
    (v : ∀ ν, Fin (r ν+1) → AlignmentAddingPair M (f i) → ℤ)
    (hv : ∀ ν, Function.Injective (alignmentNativeFiniteEvaluation
      (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (r ν) (v ν)))
    (targets : ι → Finset (Fin M)) (gap : ℕ)
    (hsmall : ∀ e : AlignmentAddingPair n i, (e.map f).sourcePivot.val < gap)
    (H : NativeRationalSubgroupFiltration
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν))) s)
    (period : ℕ) (hperiod : 0 < period)
    (sigma : Fin period → (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν))).G)
    (hRat : ∀ z, sigma z ∈ nativeSubgroupRationalHull
      (E := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν))).E) (I := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν))).I) (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν))).Γ)
    (h : ℝ → (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν))).G) (hh : Continuous h)
    (hsym : ∀ z β, SelectedAlignmentCatalogueCosetSymmetry D r v hv targets gap H
      (sigma z) (hRat z) (h β))
    (factor : Finset (Fin n) → ℚ → κ → (AlignmentAddingPair n i → ℤ) → Option ι)
    (obs : ∀ ν, (D ν).G ⧸ (D ν).Γ → ℝ)
    (hobs : ∀ ν, Continuous (obs ν))
    (requests : List (AlignmentPivotRequest n i)) (incoming : Finset (Fin n → ℚ))
    (q₀ : ℕ)
    (hint : ∀ stage ∈ selectedAlignmentCosetPlan (κ := κ) s requests,
      ∀ b ∈ alignmentAllScaleStates i (alignmentForwardOptions
        (selectedAlignmentCosetPlan (κ := κ) s requests)) incoming,
        ∀ l ∈ alignmentWordLetters stage.target.words,
          (q₀ : ℚ) * alignmentLetterScalar b l ∈ (Int.castRingHom ℚ).range)
    (b : Fin n → ℚ) (hb : b ∈ incoming) (hpos : ∀ j, 0 < b j) (θ : ℝ)
    (hfactor : ∀ route ∈ principalPivotRoutes (selectedAlignmentCosetPlan (κ := κ) s requests),
      ∀ request ∈ requests, ∀ a ∈ request.leading, ∀ word ∈ request.words, ∀ c,
      let arithmetic := alignmentJointRouteArithmetic
        q₀
        (selectedAlignmentCosetPlan (κ := κ) s requests) b route
      let stored := arithmetic.2.toAdd + alignmentAuxiliaryWord
        q₀ arithmetic.1 word
      ∃ ν, factor (insert i request.tail)
        (a * finiteScaleBlockProduct arithmetic.1 (insert i request.tail)) c stored = some ν ∧
        ∀ l ∈ word, targets ν = l.1.targetTail.image f) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν))
    letI : MeasurableSpace J.G := borel J.G
    let read := selectedAlignmentJointRouteNativeReading f i D r v hv factor obs
    let plan := selectedAlignmentCosetPlan (κ := κ) s requests
    (principalPivotRoutes plan).Nonempty ∧
      ((1 / ((principalPivotRoutes plan).card : ℝ≥0) : ℝ≥0) : ℝ≥0∞) ≤
        (nativePointMixtureProbability J H period hperiod sigma hRat h hh : Measure (J.G ⧸ J.Γ))
          (⋃ route : principalPivotRoutes plan,
            alignmentJointRouteClosedSet read θ q₀ plan b requests route.val) := by
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν))
  letI : MeasurableSpace J.G := borel J.G
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (J.G ⧸ J.Γ) := native_nilmanifold_metric_coset_borel J
  let read := selectedAlignmentJointRouteNativeReading f i D r v hv factor obs
  let plan := selectedAlignmentCosetPlan (κ := κ) s requests
  refine ⟨selected_alignment_coset_routes_nonempty (κ := κ) s requests, ?_⟩
  apply native_point_mixture_mass_ge J H period hperiod sigma hRat h hh
  · apply IsClosed.measurableSet
    apply isClosed_iUnion_of_finite
    intro route
    exact alignment_joint_route_closed read
      (selected_alignment_joint_route_native_reading_continuous f i D r v hv factor obs hobs)
      θ q₀ plan b requests route.val
  · intro z β
    obtain ⟨m,basis,w,hbasis⟩ := affineShear_native_initial_adapted_basis J H (sigma z) (hRat z)
    exact (selected_alignment_coset_closed_union_mass f i D r v hv targets gap hsmall H
      (sigma z) (hRat z) (h β) m basis w hbasis (hsym z β) factor obs hobs
      requests incoming q₀ hint b hb hpos θ hfactor).2

end Hindman168
