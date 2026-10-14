import Hindman168.SelectedAlignmentNativeWindow

namespace Hindman168
open Filter FiniteMass
open scoped Topology Classical
universe u

theorem alignment_native_actual_window_uniform_tail {s : ℕ} {ι : Type*} [Fintype ι]
    (D : ι → NativeNilmanifoldData.{u} s) (m degree : ℕ)
    {n k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A P F)
    (i : Fin n) (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i)
    (denominator : ℕ) (hdenominator : 0 < denominator)
    (Kref K c C B η : ℝ) (L : NNReal)
    (hKref : 0 < Kref) (hK : 1 ≤ K) (hc : 0 < c) (hC : 0 ≤ C)
    (hB : 0 ≤ B) (hη : 0 < η)
    (x : ℕ → Fin n → ℕ) (U : ℕ → Finset (Fin n)) (j : ℕ → T)
    (hvalid : ∀ᶠ w in atTop,
      x w ∈ (globalRawMass (F.cutoff w) (primorial w) n).support ∧
      (∀ l ∈ T, binaryDyadicCutoffGood (F.cutoff w l.val) (x w l)) ∧ U w ⊆ T)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ w in atTop, ∀ index : ι,
      ∀ (q : ℕ) (a : Fin m → ℤ), 0 < q →
      ∀ (Q : (Option (Fin m) → ℝ) → (D index).G)
        (pN : RoughVectorMvPolynomial (Option (Fin m)) (D index).E),
      RoughVectorMvDegreeLE pN degree →
      (∀ (z : ℝ) (y : Fin m → ℝ), roughVectorMvEval pN (Option.elim · z y) =
        nativeLieGlobalLogarithm (E := (D index).E) (I := (D index).I)
          (roughNativeResidualSource (D index) Q a q (Option.elim · z y))) →
      ∀ Zactual : ℕ → ℝ,
      (∀ t ∈ binaryDyadicResidueWindow ((F.modulus w : ℕ)*(primorial w)^w) (x w (j w).val),
        alignmentCubeScale F w i T (x w) /
            ((denominator : ℝ)*alignmentNaturalBlockProduct (x w) (U w)*Kref) ≤ Zactual t ∧
        Zactual t ≤ K*(alignmentCubeScale F w i T (x w) /
            ((denominator : ℝ)*alignmentNaturalBlockProduct (x w) (U w)*Kref))) →
      event (uniformFinsetMass
        (binaryDyadicResidueWindow ((F.modulus w : ℕ)*(primorial w)^w) (x w (j w).val)))
        (fun t => RoughNativeRealResidualComplexLargeIndex (D index) Q a q t t
          (Zactual t) c C L B η) < δ := by
  let Scale := fun w => ((2 ^ Nat.log2 (x w (j w).val) : ℕ) : ℝ)
  let Zref := fun w => alignmentCubeScale F w i T (x w) /
    ((denominator : ℝ)*alignmentNaturalBlockProduct (x w) (U w)*Kref)
  have hratio := alignment_dyadic_residue_ratio_tendsto hF (fun w => (j w).val)
    (fun w => x w (j w).val) (by
      filter_upwards [hvalid] with w hw
      exact (hw.2.1 (j w).val (j w).property).1.trans
        (Nat.log2_self_le (alignmentGlobalRawMass_support_positive hF _ _ hw.1 (j w).val).ne'))
  have hScale : Tendsto Scale atTop atTop := by
    apply tendsto_atTop_mono' _ _ hratio
    filter_upwards [] with w
    have hL : (1 : ℝ) ≤ (((F.modulus w : ℕ)*(primorial w)^w : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos (F.modulus w).pos
        (Nat.pow_pos (primorial_pos w))).ne'
    exact div_le_self (by positivity) hL
  have hg := alignment_raw_native_reference_real_ratios hF i T hT denominator
    hdenominator Kref hKref x U (fun w => (j w).val)
    (hvalid.mono (fun _ hw => ⟨hw.1,hw.2.2,(j _).property⟩))
  obtain ⟨R,_hR,hbound⟩ := native_finite_real_residual_rough_proportion_uniform D m degree c (C*K)
    B η L hc (mul_nonneg hC (zero_le_one.trans hK)) hB hη Scale Zref hScale hg hδ
  filter_upwards [hbound,hvalid,eventually_ge_atTop 1,
    hratio.eventually (eventually_ge_atTop (R : ℝ))] with w hw hv hwone hR
  intro index q a hq Q pN hpN hlogN Zactual hZrange
  exact alignment_native_variable_scale_window_event_lt (D index) m degree w R (Zref w)
    c C K B η δ L hF hwone (x w) hv.1 (j w).val hc.le hC hδ (hw index) hR
    q a hq Q pN hpN hlogN Zactual hZrange


theorem alignment_native_window_all_anchors_uniform_tail {s : ℕ} {ι : Type*} [Fintype ι]
    (D : ι → NativeNilmanifoldData.{u} s) (m degree : ℕ)
    {n k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A P F)
    (i : Fin n) (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i)
    (denominator : ℕ) (hdenominator : 0 < denominator)
    (Kref K c C B η : ℝ) (L : NNReal)
    (hKref : 0 < Kref) (hK : 1 ≤ K) (hc : 0 < c) (hC : 0 ≤ C)
    (hB : 0 ≤ B) (hη : 0 < η) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ w in atTop, ∀ x ∈ (globalRawMass (F.cutoff w) (primorial w) n).support,
      (∀ l ∈ T, binaryDyadicCutoffGood (F.cutoff w l.val) (x l)) → ∀ U : Finset (Fin n), U ⊆ T →
      ∀ j : T, AlignmentNativeWindowCap D m degree F w i T x U j
        denominator Kref K c C B η δ L := by
  by_cases hTnon : T.Nonempty
  · obtain ⟨j₀,hj₀⟩ := hTnon
    let V : ℕ → ((Fin n → ℕ) × Finset (Fin n) × T) → Prop := fun w a =>
      a.1 ∈ (globalRawMass (F.cutoff w) (primorial w) n).support ∧
      (∀ l ∈ T, binaryDyadicCutoffGood (F.cutoff w l.val) (a.1 l)) ∧ a.2.1 ⊆ T
    let Good : ℕ → ((Fin n → ℕ) × Finset (Fin n) × T) → Prop := fun w a =>
      AlignmentNativeWindowCap D m degree F w i T a.1 a.2.1 a.2.2
        denominator Kref K c C B η δ L
    have hV : ∀ᶠ w in atTop, ∃ a, V w a := by
      filter_upwards [alignmentGlobalRawMass_geometry hF,
        (alignment_typicalShortPosterior_success_tendsto hF i T).eventually
          (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with w hg ht
      obtain ⟨x,hx,hgood⟩ := exists_supported_of_event_pos _ _ hg.1 ht
      exact ⟨(x,∅,⟨j₀,hj₀⟩),hx,hgood.1,Finset.empty_subset T⟩
    have hselectors (a : ℕ → ((Fin n → ℕ) × Finset (Fin n) × T))
        (ha : ∀ᶠ w in atTop, V w (a w)) : ∀ᶠ w in atTop, Good w (a w) := by
      exact alignment_native_actual_window_uniform_tail D m degree hF i T hT denominator
        hdenominator Kref K c C B η L hKref hK hc hC hB hη
        (fun w => (a w).1) (fun w => (a w).2.1) (fun w => (a w).2.2) ha hδ
    have hh := rough_eventual_uniform_of_actual_selectors
      ((fun _ => 0),∅,⟨j₀,hj₀⟩) V Good hV hselectors
    filter_upwards [hh] with w hw
    intro x hx ht U hU j
    exact hw (x,U,j) ⟨hx,ht,hU⟩
  · filter_upwards [] with w
    intro x hx ht U hU j
    exact (hTnon ⟨j.val,j.property⟩).elim


theorem selected_alignment_native_window_all_anchors_tail {s : ℕ} {ι : Type*} [Fintype ι]
    (D : ι → NativeNilmanifoldData.{u} s) (m degree : ℕ)
    {N k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F)
    (pivot gap : Fin N) (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < gap)
    (denominator : ℕ) (hdenominator : 0 < denominator)
    (Kref K c C B η : ℝ) (L : NNReal)
    (hKref : 0 < Kref) (hK : 1 ≤ K) (hc : 0 < c) (hC : 0 ≤ C)
    (hB : 0 ≤ B) (hη : 0 < η) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ w in atTop, ∀ x ∈ (globalRawMass (F.cutoff w) (primorial w) N).support,
      (∀ l ∈ T, binaryDyadicCutoffGood (F.cutoff w l.val) (x l)) → ∀ U : Finset (Fin N), U ⊆ T →
      ∀ j : T, AlignmentNativeWindowCap D m degree (alignmentGeometryWithGap F pivot gap)
        w pivot T x U j denominator Kref K c C B η δ L := by
  have hh := alignment_native_window_all_anchors_uniform_tail D m degree hF gap T hT
    denominator hdenominator Kref K c C B η L hKref hK hc hC hB hη hδ
  filter_upwards [hh] with w hw
  intro x hx ht U hU j
  simpa only [AlignmentNativeWindowCap, alignmentGeometryWithGap_modulus,
    alignmentGeometryWithGap_cubeScale] using hw x hx ht U hU j

theorem selected_alignment_native_compact_test_window_all_anchors_tail {s : ℕ} {κ : Type*} [Fintype κ]
    (D : NativeNilmanifoldData.{u} s) (degree : ℕ)
    {n k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A P F)
    (i gap : Fin n) (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < gap)
    (denominator : ℕ) (hdenominator : 0 < denominator)
    (Kref K c C η : ℝ) (hKref : 0 < Kref) (hK : 1 ≤ K)
    (hc : 0 < c) (hC : 0 ≤ C) (hη : 0 < η) {δ : ℝ} (hδ : 0 < δ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace (D.G ⧸ D.Γ) := native_metric_quotient_compact D
    ∀ H : Set C(D.G ⧸ D.Γ,ℂ), IsCompact H →
    ∃ B L : ℝ, 0 < B ∧ 0 < L ∧
    ∀ᶠ w in atTop, ∀ x ∈ (globalRawMass (F.cutoff w) (primorial w) n).support,
      (∀ l ∈ T, binaryDyadicCutoffGood (F.cutoff w l.val) (x l)) →
      ∀ U : Finset (Fin n), U ⊆ T → ∀ j : T,
      ∀ (q : ℕ) (a : κ → ℤ), 0 < q →
      ∀ (Q : (Option κ → ℝ) → D.G) (pN : RoughVectorMvPolynomial (Option κ) D.E),
      RoughVectorMvDegreeLE pN degree →
      (∀ (z : ℝ) (y : κ → ℝ), roughVectorMvEval pN (Option.elim · z y) =
        nativeLieGlobalLogarithm (E := D.E) (I := D.I)
          (roughNativeResidualSource D Q a q (Option.elim · z y))) →
      ∀ Zactual : ℕ → ℝ,
      (∀ t ∈ binaryDyadicResidueWindow ((F.modulus w : ℕ)*(primorial w)^w) (x j.val),
        alignmentCubeScale (alignmentGeometryWithGap F i gap) w i T x /
          ((denominator : ℝ)*alignmentNaturalBlockProduct x U*Kref) ≤ Zactual t ∧
        Zactual t ≤ K*(alignmentCubeScale (alignmentGeometryWithGap F i gap) w i T x /
          ((denominator : ℝ)*alignmentNaturalBlockProduct x U*Kref))) →
      event (uniformFinsetMass
        (binaryDyadicResidueWindow ((F.modulus w : ℕ)*(primorial w)^w) (x j.val)))
        (fun t => RoughNativeRealResidualTestFamilyLargeIndex D Q a q t t
          (Zactual t) c C η H) < δ := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro H hH
  obtain ⟨B,L,hB,hL,happrox⟩ := rough_native_real_residual_compact_family_bounds D η hη H hH
  refine ⟨B,L,hB,hL,?_⟩
  have hh := selected_alignment_native_window_all_anchors_tail (fun _ : Unit => D)
    (Fintype.card κ) degree hF i gap T hT denominator hdenominator Kref K c C B (η/2)
    (Real.toNNReal L) hKref hK hc hC hB.le (by positivity) hδ
  filter_upwards [hh] with w hw
  intro x hx htyp U hU j q a hq Q pN hp hlog Zactual hZ
  exact alignment_native_window_cap_test_family (fun _ : Unit => D)
    (Fintype.card κ) degree (Fintype.equivFin κ) (alignmentGeometryWithGap F i gap) w i T x U j denominator
    Kref K c C B η δ (Real.toNNReal L) hη (hw x hx htyp U hU j)
    () q a hq Q pN hp hlog Zactual hZ H happrox



end Hindman168
