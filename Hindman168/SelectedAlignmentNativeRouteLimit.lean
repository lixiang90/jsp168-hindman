import Hindman168.SelectedAlignmentCosetMassMixture
import Hindman168.SelectedAlignmentRouteThresholdLimit

/-! The actual same-source point law, actual small-letter symmetries and
uniformly convergent observers imply the quantitative prelimit route bound.
All coset lifts and closed-cover assertions are proved by the imported
geometric and recurrence interfaces, not assumed in this statement. -/
namespace Hindman168
open Filter MeasureTheory Module
open scoped Topology Manifold ContDiff Classical ENNReal NNReal
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem selected_alignment_native_route_empirical_liminf
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
    (obs : ∀ ν, C((D ν).G ⧸ (D ν).Γ, ℝ))
    (obs_m : ℕ → ∀ ν, C((D ν).G ⧸ (D ν).Γ, ℝ))
    (hconv : ∀ ν, TendstoUniformly (fun m => obs_m m ν) (obs ν) atTop)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (P : ℕ → ℝ → (nativeFinitePiData
      (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν))).G)
    (hlaw : NativeResidueLocalHaarLaw
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν)))
      H L P period hperiod sigma hRat h)
    (requests : List (AlignmentPivotRequest n i)) (incoming : Finset (Fin n → ℚ))
    (q₀ : ℕ)
    (hint : ∀ stage ∈ selectedAlignmentCosetPlan (κ := κ) s requests,
      ∀ b ∈ alignmentAllScaleStates i (alignmentForwardOptions
        (selectedAlignmentCosetPlan (κ := κ) s requests)) incoming,
        ∀ l ∈ alignmentWordLetters stage.target.words,
          (q₀ : ℚ) * alignmentLetterScalar b l ∈ (Int.castRingHom ℚ).range)
    (b : Fin n → ℚ) (hb : b ∈ incoming) (hpos : ∀ j, 0 < b j) (θ : ℝ) (hθ : 0 < θ)
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
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : BorelSpace (J.G ⧸ J.Γ) := native_nilmanifold_metric_coset_borel J
    let plan := selectedAlignmentCosetPlan (κ := κ) s requests
    ((1 / ((principalPivotRoutes plan).card : ℝ≥0) : ℝ≥0) : ℝ≥0∞) ≤
      atTop.liminf (fun m =>
        (finiteEmpiricalProbability (Finset.Ico 0 ⌊L m⌋)
          (fun z => (P m (z : ℝ) : J.G ⧸ J.Γ)) (1 : J.G) : Measure (J.G ⧸ J.Γ))
        (selectedAlignmentRouteActualSet
          (selectedAlignmentJointRouteNativeReading f i D r v hv factor (fun ν => obs_m m ν))
          θ q₀ plan b requests (principalPivotRoutes plan))) := by
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν))
  letI : MeasurableSpace J.G := borel J.G
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (J.G ⧸ J.Γ) := native_nilmanifold_metric_coset_borel J
  let read := selectedAlignmentJointRouteNativeReading f i D r v hv factor (fun ν => obs ν)
  let reads := fun m => selectedAlignmentJointRouteNativeReading f i D r v hv factor (fun ν => obs_m m ν)
  let plan := selectedAlignmentCosetPlan (κ := κ) s requests
  have hmass := (selected_alignment_mixture_closed_union_mass f i D r v hv targets gap hsmall
    H period hperiod sigma hRat h hh hsym factor (fun ν => obs ν) (fun ν => (obs ν).continuous)
    requests incoming q₀ hint b hb hpos θ hfactor).2
  have he : ∀ ν, ∀ᶠ m in atTop, ∀ z, |obs_m m ν z - obs ν z| < θ/4 := by
    intro ν
    simpa only [Real.dist_eq, abs_sub_comm] using
      (Metric.tendstoUniformly_iff.mp (hconv ν)) (θ/4) (by positivity)
  have herr : ∀ᶠ m in atTop, ∀ B a c stored query y,
      |reads m B a c stored query y - read B a c stored query y| < θ/4 := by
    filter_upwards [Filter.eventually_all.mpr he] with m hm
    intro B a c stored query y
    dsimp only [reads, read, selectedAlignmentJointRouteNativeReading]
    cases factor B a c stored with
    | none => simpa using (show (0 : ℝ) < θ/4 by positivity)
    | some ν => exact hm ν _
  have hweak := native_original_point_weak_limit J H L hL P period hperiod sigma hRat h hh hlaw
  apply selected_alignment_route_closed_mass_actual_liminf atTop _ _ hweak read reads
    (fun B a c stored query => selected_alignment_joint_route_native_reading_continuous
      f i D r v hv factor (fun ν => obs ν) (fun ν => (obs ν).continuous) B a c stored query)
    θ hθ q₀ plan b requests (principalPivotRoutes plan) _ _ hmass
  filter_upwards [herr] with m hm
  intro route hr j y
  exact ⟨hm _ _ _ _ _ _,hm _ _ _ _ _ _⟩

end Hindman168
