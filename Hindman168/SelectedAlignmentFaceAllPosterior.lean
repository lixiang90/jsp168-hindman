import Hindman168.AlignmentOriginalProductAllFacesPosterior
import Hindman168.SelectedAlignmentFaceProductFailure
import Hindman168.SelectedAlignmentFaceFiniteFamily

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
theorem selected_alignment_original_product_all_faces_posterior_vanishing
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F) (gap : Fin N) (hgap : gap ≤ i)
    (q₀ : ℕ) (hq : 0 < q₀) (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < gap)
    (d : ℕ) (hd : 0 < d) (c C : ℝ) (K : ℕ)
    (hc : 0 < c) (hC : 0 ≤ C) (hK : C+1 ≤ (K : ℝ))
    (slots : ι → AlignmentAddingPair N i → ℤ) (B : ι → ℝ) (L : ι → NNReal) (hB : ∀ ν, 0 ≤ B ν)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ w in atTop, ∀ x ∈ (globalRawMass (F.cutoff w) (primorial w) N).support,
      alignmentTypicalShortPosterior (alignmentGeometryWithGap F i gap) w i T x →
      ∀ (shift : ι → AlignmentAddingPair N i → ℤ) (g a : ∀ ν, (D ν).G),
      event (conditionMass (globalRawMass (F.cutoff w) (primorial w) N)
        (fun y => alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T y=alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T x))
        (selectedAlignmentOriginalProductAllFacesFailure (β := κ) D (alignmentGeometryWithGap F i gap) gap q₀ w T d shift slots g a B L c C ε) < δ := by
  letI := alignmentAddingPairFintype N i
  let χ := ({e : AlignmentAddingPair N i // e.targetTail=T ∧ e.sourcePivot < gap} × κ) × (ι → κ → Fin 2)
  let weight : χ → ι → κ → ℤ := fun z ν j => (z.2 ν j).val
  have hh := selected_alignment_original_product_face_finite_family (χ := χ) D n v hv r b
    hF gap hgap q₀ hq T hT d hd c C K hc hC hK (fun _ => slots) weight (fun _ => B) (fun _ => L)
    (fun _ => hB) (fun z => z.1.1.val) (fun z => z.1.1.property.1) (fun z => z.1.1.property.2) (fun z => z.1.2) hε hδ
  filter_upwards [hh,alignmentGlobalRawMass_geometry hF] with w hw hraw
  intro x hx htyp shift g a
  let μ := conditionMass (globalRawMass (F.cutoff w) (primorial w) N)
    (fun y => alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T y=alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T x)
  let E : (Fin N → ℕ) → Prop := fun y => ∃ z : χ,
    alignmentOriginalProductFaceFailure D (alignmentGeometryWithGap F i gap) q₀ w T d shift slots (weight z) g a B L c C ε z.1.1.val z.1.2 y
  have hcap : event μ E < δ := hw x hx htyp (fun _ => shift) (fun _ => g) (fun _ => a)
  apply lt_of_le_of_lt _ hcap
  apply event_mono_on_support μ _ E (conditionMass_nonneg _ _ hraw.1)
  intro y _hy hbad
  obtain ⟨originalWeight,hbits,e,he,hegap,j,hface⟩ := hbad
  obtain ⟨bits,hbitsEq⟩ := alignment_zero_one_vertex_weights_represent originalWeight hbits
  have hweights : weight ((⟨e,he,hegap⟩,j),bits)=originalWeight := by
    funext ν j
    exact hbitsEq ν j
  refine ⟨((⟨e,he,hegap⟩,j),bits),?_⟩
  rw [hweights]
  exact hface


end Hindman168
