import Hindman168.SelectedAlignmentGeometryView
import Hindman168.AlignmentNativeCompactTestWindow

/-! The analytic rough window depends on the tail and model gap, not on the
raw pivot value. Its original theorem at the padding index therefore gives
the exact selected-gap cap, without admissibility of the data-only view. -/
namespace Hindman168
open Filter FiniteMass
open scoped Topology
universe u

theorem alignmentGeometryWithGap_cubeScale {N : ℕ} (F : MasterParameterFamily)
    (pivot gap : Fin N) (w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ) :
    alignmentCubeScale (alignmentGeometryWithGap F pivot gap) w pivot T x =
      alignmentCubeScale F w gap T x := by
  simp only [alignmentCubeScale, alignmentShortBinVolume, alignmentGeometryWithGap_gap,
    alignmentGeometryWithGap_modulus]

theorem selected_alignment_native_window_all_anchors {s : ℕ} {ι : Type*} [Fintype ι]
    (D : ι → NativeNilmanifoldData.{u} s) (m degree : ℕ)
    {N k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F)
    (pivot gap : Fin N) (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < gap)
    (denominator : ℕ) (hdenominator : 0 < denominator)
    (Kref K c C B η : ℝ) (L : NNReal)
    (hKref : 0 < Kref) (hK : 1 ≤ K) (hc : 0 < c) (hC : 0 ≤ C)
    (hB : 0 ≤ B) (hη : 0 < η) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ w in atTop, ∀ x ∈ (globalRawMass (F.cutoff w) (primorial w) N).support,
      alignmentTypicalShortPosterior F w gap T x → ∀ U : Finset (Fin N), U ⊆ T →
      ∀ j : T, AlignmentNativeWindowCap D m degree (alignmentGeometryWithGap F pivot gap)
        w pivot T x U j denominator Kref K c C B η δ L := by
  have hh := alignment_native_window_all_anchors_uniform D m degree hF gap T hT
    denominator hdenominator Kref K c C B η L hKref hK hc hC hB hη hδ
  filter_upwards [hh] with w hw
  intro x hx ht U hU j
  simpa only [AlignmentNativeWindowCap, alignmentGeometryWithGap_modulus,
    alignmentGeometryWithGap_cubeScale] using hw x hx ht U hU j

theorem selected_alignment_native_compact_test_window_all_anchors {s : ℕ} {κ : Type*} [Fintype κ]
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
      alignmentTypicalShortPosterior F w gap T x →
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
  have hh := selected_alignment_native_window_all_anchors (fun _ : Unit => D)
    (Fintype.card κ) degree hF i gap T hT denominator hdenominator Kref K c C B (η/2)
    (Real.toNNReal L) hKref hK hc hC hB.le (by positivity) hδ
  filter_upwards [hh] with w hw
  intro x hx htyp U hU j q a hq Q pN hp hlog Zactual hZ
  exact alignment_native_window_cap_test_family (fun _ : Unit => D)
    (Fintype.card κ) degree (Fintype.equivFin κ) (alignmentGeometryWithGap F i gap) w i T x U j denominator
    Kref K c C B η δ (Real.toNNReal L) hη (hw x hx htyp U hU j)
    () q a hq Q pN hp hlog Zactual hZ H happrox


end Hindman168
