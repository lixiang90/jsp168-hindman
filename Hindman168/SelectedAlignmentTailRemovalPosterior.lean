import Hindman168.SelectedAlignmentTailRemovalEvent
import Hindman168.SelectedAlignmentPosteriorFiber

/-! Integrate PROVED actual joint-source rest-fiber bounds against the original
product windows, then use the actual short-exposure posterior domination.
No conditional independence or supplied analytic fiber cap is assumed. -/
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

theorem selected_alignment_joint_tail_removal_posterior_union_bound
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F)
    (gap : Fin N) (hgap : gap ≤ i) (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < gap)
    (d : ℕ) (hd : 0 < d) (c C η : ℝ) (hc : 0 < c) (hC : 0 ≤ C) (hη : 0 < η)
    (slots : ι → AlignmentAddingPair N i → ℤ) (B : ι → ℝ) (L : ι → NNReal)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ w in atTop, ∀ x ∈ (globalRawMass (F.cutoff w) (primorial w) N).support,
      alignmentTypicalShortPosterior (alignmentGeometryWithGap F i gap) w i T x →
      ∀ U : T → Finset (Fin N), (∀ j, U j ⊆ T ∧ j.val ∉ U j) →
      ∀ (q₀ : ℕ) (Y rho : ℤ) (residueChoice : T → Option κ → ℤ)
        (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G),
      event (conditionMass (globalRawMass (F.cutoff w) (primorial w) N)
        (fun y => alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T y=alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T x))
        (fun y => ∃ j : T, alignmentJointTailRemovalEvent D n v hv r b (alignmentGeometryWithGap F i gap) q₀ w T (U j) x j d
          Y rho (residueChoice j) shift slots weight g a B L c C η (fun k : T => y k.val)) ≤ (3*2^T.card)*(T.card : ℝ)*δ := by
  have hfiber := selected_alignment_joint_tail_removal_fiber_event_bound (κ := κ) D n v hv r b
    hF gap T hT d hd c C η hc hC hη slots B L hδ
  have hposterior := selected_alignment_typical_short_posterior_fiber_union_eventually hF i gap hgap T
    (fun j hj => (hT j hj).trans_le hgap)
  filter_upwards [hfiber,hposterior] with w hf hp
  intro x hx htyp U hU q₀ Y rho residueChoice shift weight g a
  apply hp x hx htyp
    (fun j tail => alignmentJointTailRemovalEvent D n v hv r b (alignmentGeometryWithGap F i gap) q₀ w T (U j) x j d
      Y rho (residueChoice j) shift slots weight g a B L c C η tail) δ
  intro j rest hrest
  exact hf x hx htyp.1 (U j) (hU j).1 j (hU j).2 rest hrest q₀ Y rho (residueChoice j) shift weight g a

theorem selected_alignment_joint_tail_removal_posterior_uniform_vanishing
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F)
    (gap : Fin N) (hgap : gap ≤ i) (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < gap)
    (d : ℕ) (hd : 0 < d) (c C η : ℝ) (hc : 0 < c) (hC : 0 ≤ C) (hη : 0 < η)
    (slots : ι → AlignmentAddingPair N i → ℤ) (B : ι → ℝ) (L : ι → NNReal)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w in atTop, ∀ x ∈ (globalRawMass (F.cutoff w) (primorial w) N).support,
      alignmentTypicalShortPosterior (alignmentGeometryWithGap F i gap) w i T x →
      ∀ U : T → Finset (Fin N), (∀ j, U j ⊆ T ∧ j.val ∉ U j) →
      ∀ (q₀ : ℕ) (Y rho : ℤ) (residueChoice : T → Option κ → ℤ)
        (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G),
      event (conditionMass (globalRawMass (F.cutoff w) (primorial w) N)
        (fun y => alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T y=alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T x))
        (fun y => ∃ j : T, alignmentJointTailRemovalEvent D n v hv r b (alignmentGeometryWithGap F i gap) q₀ w T (U j) x j d
          Y rho (residueChoice j) shift slots weight g a B L c C η (fun k : T => y k.val)) < ε := by
  let C₀ : ℝ := (3*2^T.card)*(T.card : ℝ)
  let δ := ε/(C₀+1)
  have hC₀ : 0 ≤ C₀ := by dsimp only [C₀]; positivity
  have hδ : 0 < δ := div_pos hε (by positivity)
  have he : (C₀+1)*δ=ε := by dsimp only [δ]; field_simp
  have hh := selected_alignment_joint_tail_removal_posterior_union_bound (κ := κ) D n v hv r b
    hF gap hgap T hT d hd c C η hc hC hη slots B L hδ
  filter_upwards [hh] with w hw
  intro x hx htyp U hU q₀ Y rho residueChoice shift weight g a
  have hb := hw x hx htyp U hU q₀ Y rho residueChoice shift weight g a
  change _ ≤ C₀*δ at hb
  nlinarith

end Hindman168
