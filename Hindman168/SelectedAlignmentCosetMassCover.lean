import Hindman168.SelectedAlignmentCosetMassRecurrence
import Hindman168.SelectedAlignmentCatalogueLettersReadings
import Hindman168.PositivePrincipalSumMassJointHaar

namespace Hindman168
open MeasureTheory Module
open scoped Topology Manifold ContDiff BigOperators ENNReal NNReal Classical
universe u
attribute [local instance] lieGroup_smooth_min_three alignmentAddingPairFintype

/-- The actual selected joint coset has a fixed finite closed union of mass
at least 1/Q. Both own-letter equivariance and pointwise recurrence coverage
are derived. The chosen plan/denominator do not depend on the model or theta. -/
theorem selected_alignment_coset_closed_union_mass
    {ι κ : Type} [Fintype ι] [Finite κ] {n M : ℕ} (f : Fin n ↪o Fin M) (i : Fin n) {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) (r : ι → ℕ)
    (v : ∀ ν, Fin (r ν+1) → AlignmentAddingPair M (f i) → ℤ)
    (hv : ∀ ν, Function.Injective (alignmentNativeFiniteEvaluation
      (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (r ν) (v ν)))
    (targets : ι → Finset (Fin M)) (gap : ℕ)
    (hsmall : ∀ e : AlignmentAddingPair n i, (e.map f).sourcePivot.val < gap)
    (H : NativeRationalSubgroupFiltration
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν))) s)
    (ρ : (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν))).G)
    (hρ : ρ ∈ nativeSubgroupRationalHull
      (E := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν))).E)
      (I := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν))).I)
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν))).Γ)
    (h : (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν))).G)
    (m : ℕ)
    (basis : Basis (Fin m) ℝ (nativeRationalLayerOrbitData
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν))) H 1 ρ hρ).E)
    (w : Fin m → ℕ)
    (hbasis : ∀ j, 1 ≤ w j ∧ w j ≤ s ∧
      basis j ∈ affineShearNativeInitialFiltration
        (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν))) H ρ hρ (w j) ∧
      affineShearNativeInitialFiltration
        (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν))) H ρ hρ (w j+1) ≤
          (basis.coord j).ker)
    (hsym : SelectedAlignmentCatalogueCosetSymmetry D r v hv targets gap H ρ hρ h)
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
        nativeRationalLayerHaarImage J H 1 ρ hρ h
          (⋃ route : principalPivotRoutes plan,
            alignmentJointRouteClosedSet read θ q₀ plan b requests route.val) := by
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν))
  letI : MeasurableSpace J.G := borel J.G
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (J.G ⧸ J.Γ) := native_nilmanifold_metric_coset_borel J
  let K := nativeRationalLayerOrbitData J H 1 ρ hρ
  let projection := fun z => nativeRationalLayerOrbitMap J H 1 ρ hρ h (weightedShearNativeProjection K basis z)
  let read := selectedAlignmentJointRouteNativeReading f i D r v hv factor obs
  let plan := selectedAlignmentCosetPlan (κ := κ) s requests
  obtain ⟨L,hL⟩ := selected_alignment_joint_native_letters_reading_equivariance f i D r v hv
    targets gap hsmall H ρ hρ h m basis w hbasis hsym factor obs
  have hcover : ∀ z : Fin m → ℝ, ∃ route ∈ principalPivotRoutes plan,
      projection ((principalPivotRouteValue q₀ L plan b route).2 • z) ∈
        alignmentJointRouteClosedSet read θ q₀ plan b requests route := by
    apply selected_alignment_coset_plan_closed_cover_of_denominators s requests incoming q₀ hint (Fin m) (J.G ⧸ J.Γ) w (fun j => (hbasis j).2.1.trans (Nat.le_succ s))
      L projection read θ b hb hpos
    intro route hr request hreq a ha word hw c
    obtain ⟨ν,hν,htarget⟩ := hfactor route hr request hreq a ha word hw c
    dsimp only
    intro l hl query z
    exact hL l.1 _ _ _ _ query ν hν (htarget l hl) z
  have hne : (principalPivotRoutes plan).Nonempty :=
    selected_alignment_coset_routes_nonempty (κ := κ) s requests
  letI : Nonempty (principalPivotRoutes plan) := ⟨⟨hne.choose,hne.choose_spec⟩⟩
  refine ⟨hne, ?_⟩
  have hh := principal_original_joint_haar_closed_cover J H ρ hρ basis w hbasis h
    (fun route : principalPivotRoutes plan => (principalPivotRouteValue q₀ L plan b route.val).2)
    (fun route : principalPivotRoutes plan => alignmentJointRouteClosedSet read θ q₀ plan b requests route.val)
    (fun route => alignment_joint_route_closed read
      (selected_alignment_joint_route_native_reading_continuous f i D r v hv factor obs hobs)
      θ q₀ plan b requests route.val)
    (by intro z; obtain ⟨route,hr,hmem⟩ := hcover z; exact ⟨⟨route,hr⟩,hmem⟩)
  simpa only [Fintype.card_coe] using hh
end Hindman168
