import Hindman168.SelectedAlignmentNativeTailWindow
import Hindman168.AlignmentJointResidualTestFamily
import Hindman168.AlignmentJointRemovedNativeSource

/-! Selected-padding all-anchor original joint-observation rough cap with the ACTUAL joint
one-factor source and its proved degree/log packet. Retained arithmetic and
normalized scale-range remain explicit geometric inputs, not analytic oracles. -/
namespace Hindman168
open Module Filter FiniteMass
open scoped Manifold ContDiff BigOperators Classical
universe u

variable {ι : Type} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))
  (r : ι → ℕ) (b : ∀ ν, Basis (Fin (r ν)) ℝ (alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)).E)

theorem selected_alignment_joint_removed_original_test_window_all_anchors
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F)
    (gap : Fin N) (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < gap)
    (denominator : ℕ) (hdenominator : 0 < denominator)
    (Kref K c C η : ℝ) (hKref : 0 < Kref) (hK : 1 ≤ K)
    (hc : 0 < c) (hC : 0 ≤ C) (hη : 0 < η) {δ : ℝ} (hδ : 0 < δ)
    (slots : ι → AlignmentAddingPair N i → ℤ) (B : ι → ℝ) (L : ι → NNReal) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    ∃ B' L' : ℝ, 0 < B' ∧ 0 < L' ∧
    ∀ᶠ w in atTop, ∀ x ∈ (globalRawMass (F.cutoff w) (primorial w) N).support,
      (∀ l ∈ T, binaryDyadicCutoffGood (F.cutoff w l.val) (x l)) →
      ∀ U : Finset (Fin N), U ⊆ T → ∀ j : T,
      ∀ (q : ℕ) (residue : Option κ → ℤ), 0 < q →
      ∀ (q₀ : ℕ) (frozen : Fin N → ℝ)
        (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G),
      ∀ Zactual : ℕ → ℝ,
      (∀ t ∈ binaryDyadicResidueWindow ((F.modulus w : ℕ)*(primorial w)^w) (x j.val),
        alignmentCubeScale (alignmentGeometryWithGap F i gap) w i T x /
          ((denominator : ℝ)*alignmentNaturalBlockProduct x U*Kref) ≤ Zactual t ∧
        Zactual t ≤ K*(alignmentCubeScale (alignmentGeometryWithGap F i gap) w i T x /
          ((denominator : ℝ)*alignmentNaturalBlockProduct x U*Kref))) →
      let Q := alignmentJointRemovedNativeSource D n v hv r b (alignmentGeometryWithGap F i gap) q₀ w T x j.val frozen shift weight g a
      event (uniformFinsetMass
        (binaryDyadicResidueWindow ((F.modulus w : ℕ)*(primorial w)^w) (x j.val)))
        (fun t => RoughNativeRealResidualTestFamilyLargeIndex J Q residue q t t
          (Zactual t) c C η (alignmentJointOriginalTestFamily D n v hv slots B L)) < δ := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  obtain ⟨B',L',hB',hL',hh⟩ := selected_alignment_native_compact_test_window_all_anchors_tail
    (κ := Option κ) J (((s*s+1)^(s+1))*max 1 T.card)
    hF i gap T hT denominator hdenominator Kref K c C η hKref hK hc hC hη hδ
    (alignmentJointOriginalTestFamily D n v hv slots B L)
    (alignment_joint_original_test_family_compact D n v hv slots B L)
  refine ⟨B',L',hB',hL',?_⟩
  filter_upwards [hh] with w hw
  intro x hx htyp U hU j q residue hq q₀ frozen shift weight g a Zactual hZ
  have hpkt := alignment_joint_removed_native_residual_packet D n v hv r b
    (alignmentGeometryWithGap F i gap) q₀ w T x j.val frozen shift weight g a residue q
  exact hw x hx htyp U hU j q residue hq
    (alignmentJointRemovedNativeSource D n v hv r b (alignmentGeometryWithGap F i gap) q₀ w T x j.val frozen shift weight g a)
    (roughNativeResidualPolynomial
      (alignmentJointRemovedNativePolynomial D n v hv r b (alignmentGeometryWithGap F i gap) q₀ w T x j.val frozen shift weight g a) residue q)
    hpkt.1 hpkt.2 Zactual hZ

end Hindman168
