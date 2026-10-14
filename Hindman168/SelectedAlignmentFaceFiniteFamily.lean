import Hindman168.AlignmentOriginalProductFaceFiniteFamily
import Hindman168.SelectedAlignmentJointSourceTransportFaceProduct
import Hindman168.SelectedAlignmentBoxRemovalChoices
import Hindman168.SelectedAlignmentTerminalTranslation
import Hindman168.SelectedAlignmentFacePosterior

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

include n v hv r b in
theorem selected_alignment_original_product_face_finite_family
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F) (gap : Fin N) (hgap : gap ≤ i)
    (q₀ : ℕ) (hq : 0 < q₀) (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < gap)
    (d : ℕ) (hd : 0 < d) (c C : ℝ) (K : ℕ)
    (hc : 0 < c) (hC : 0 ≤ C) (hK : C+1 ≤ (K : ℝ))
    {χ : Type*} [Fintype χ]
    (slots : χ → ι → AlignmentAddingPair N i → ℤ) (weight : χ → ι → κ → ℤ)
    (B : χ → ι → ℝ) (L : χ → ι → NNReal) (hB : ∀ z ν, 0 ≤ B z ν)
    (pair : χ → AlignmentAddingPair N i) (hpair : ∀ z, (pair z).targetTail=T) (hpairgap : ∀ z, (pair z).sourcePivot < gap) (coordinate : χ → κ)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ w in atTop, ∀ x ∈ (globalRawMass (F.cutoff w) (primorial w) N).support,
      alignmentTypicalShortPosterior (alignmentGeometryWithGap F i gap) w i T x →
      ∀ (shift : χ → ι → AlignmentAddingPair N i → ℤ) (g a : ∀ _z : χ, ∀ ν, (D ν).G),
      event (conditionMass (globalRawMass (F.cutoff w) (primorial w) N)
        (fun y => alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T y=alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T x))
        (fun y => ∃ z : χ, alignmentOriginalProductFaceFailure D (alignmentGeometryWithGap F i gap) q₀ w T d
          (shift z) (slots z) (weight z) (g z) (a z) (B z) (L z) c C ε (pair z) (coordinate z) y) < δ := by
  have hTi : ∀ j ∈ T, j < i := fun j hj => (hT j hj).trans_le hgap
  let δ' := δ/((Fintype.card χ : ℝ)+1)
  have hδ' : 0 < δ' := div_pos hδ (by positivity)
  have he : ((Fintype.card χ : ℝ)+1)*δ'=δ := by dsimp only [δ']; field_simp
  have hh (z : χ) := selected_alignment_original_product_face_posterior_vanishing D n v hv r b
    hF gap hgap q₀ hq T hT d hd c C K hc hC hK (slots z) (weight z) (B z) (L z) (hB z)
    (pair z) (hpair z) (hpairgap z) (coordinate z) hε hδ'
  have hall : ∀ᶠ w in atTop, ∀ z : χ,
      ∀ x ∈ (globalRawMass (F.cutoff w) (primorial w) N).support,
      alignmentTypicalShortPosterior (alignmentGeometryWithGap F i gap) w i T x →
      ∀ (shift : ι → AlignmentAddingPair N i → ℤ) (g a : ∀ ν, (D ν).G),
      event (conditionMass (globalRawMass (F.cutoff w) (primorial w) N)
        (fun y => alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T y=alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T x))
        (alignmentOriginalProductFaceFailure D (alignmentGeometryWithGap F i gap) q₀ w T d shift (slots z) (weight z) g a
          (B z) (L z) c C ε (pair z) (coordinate z)) < δ' :=
    Filter.eventually_all.mpr hh
  filter_upwards [hall,alignmentGlobalRawMass_geometry hF] with w hw hraw
  intro x hx htyp shift g a
  let μ := conditionMass (globalRawMass (F.cutoff w) (primorial w) N)
    (fun y => alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T y=alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T x)
  let E : χ → (Fin N → ℕ) → Prop := fun z => alignmentOriginalProductFaceFailure D (alignmentGeometryWithGap F i gap) q₀ w T d
    (shift z) (slots z) (weight z) (g z) (a z) (B z) (L z) c C ε (pair z) (coordinate z)
  have hbound : event μ (fun y => ∃ z : χ, E z y) ≤ (Fintype.card χ : ℝ)*δ' := by
    have heq : (fun y => ∃ z : χ, E z y)=(fun y => ∃ z ∈ (Finset.univ : Finset χ), E z y) := by
      funext y; simp
    rw [heq]
    apply (event_union_bound μ Finset.univ E (conditionMass_nonneg _ _ hraw.1)).trans
    calc
      _ ≤ ∑ _z : χ, δ' := Finset.sum_le_sum (fun z _ => (hw z x hx htyp (shift z) (g z) (a z)).le)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  change event μ (fun y => ∃ z : χ, E z y) < δ
  nlinarith


end Hindman168
