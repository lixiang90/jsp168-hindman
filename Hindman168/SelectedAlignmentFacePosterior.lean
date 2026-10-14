import Hindman168.AlignmentOriginalProductFacePosterior
import Hindman168.SelectedAlignmentJointSourceTransportFaceProduct
import Hindman168.SelectedAlignmentBoxRemovalChoices
import Hindman168.SelectedAlignmentTerminalTranslation
import Hindman168.SelectedAlignmentFaceTerminal
import Hindman168.SelectedAlignmentFaceRemoval

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
theorem selected_alignment_original_product_face_posterior_vanishing
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F) (gap : Fin N) (hgap : gap ≤ i)
    (q₀ : ℕ) (hq : 0 < q₀) (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < gap)
    (d : ℕ) (hd : 0 < d) (c C : ℝ) (K : ℕ)
    (hc : 0 < c) (hC : 0 ≤ C) (hK : C+1 ≤ (K : ℝ))
    (slots : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ)
    (B : ι → ℝ) (L : ι → NNReal) (hB : ∀ ν, 0 ≤ B ν)
    (e : AlignmentAddingPair N i) (he : e.targetTail=T) (hegap : e.sourcePivot < gap) (j : κ)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ w in atTop, ∀ x ∈ (globalRawMass (F.cutoff w) (primorial w) N).support,
      alignmentTypicalShortPosterior (alignmentGeometryWithGap F i gap) w i T x →
      ∀ (shift : ι → AlignmentAddingPair N i → ℤ) (g a : ∀ ν, (D ν).G),
      event (conditionMass (globalRawMass (F.cutoff w) (primorial w) N)
        (fun y => alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T y=alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T x))
        (alignmentOriginalProductFaceFailure D (alignmentGeometryWithGap F i gap) q₀ w T d shift slots weight g a B L c C ε e j) < δ := by
  have hTi : ∀ j ∈ T, j < i := fun j hj => (hT j hj).trans_le hgap
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  have hε' : 0 < ε/3 := by positivity
  have hδ' : 0 < δ/2 := by positivity
  let faceSlots := fun ν => slots ν+Pi.single e (weight ν j)
  have h0 := selected_alignment_original_product_removal_posterior_vanishing (κ := κ) D n v hv r b
    hF gap hgap q₀ hq T hT d hd c C K hc hC hK slots B L hε' hδ'
  have h1 := selected_alignment_original_product_removal_posterior_vanishing (κ := κ) D n v hv r b
    hF gap hgap q₀ hq T hT d hd c C K hc hC hK faceSlots B L hε' hδ'
  have ht := selected_alignment_joint_actual_terminal_product_face_eventually (κ := κ) D n v hv r b
    hF gap hgap q₀ hq T hT d hd c C K hc hC hK slots B L hB hε'
  filter_upwards [h0,h1,ht,alignmentGlobalRawMass_geometry hF] with w hw0 hw1 hwt hraw
  intro x hx htyp shift g a
  let μ := conditionMass (globalRawMass (F.cutoff w) (primorial w) N)
    (fun y => alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T y=alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T x)
  let E0 := alignmentOriginalProductRemovalFailure D n v hv r b (alignmentGeometryWithGap F i gap) q₀ w T x d hd shift slots weight g a B L c C (ε/3)
  let E1 := alignmentOriginalProductRemovalFailure D n v hv r b (alignmentGeometryWithGap F i gap) q₀ w T x d hd shift faceSlots weight g a B L c C (ε/3)
  have hm : ∀ y, 0 ≤ μ y := conditionMass_nonneg _ _ hraw.1
  have hcap0 : event μ E0 < δ/2 := hw0 x hx htyp shift weight g a
  have hcap1 : event μ E1 < δ/2 := hw1 x hx htyp shift weight g a
  have hinclude : event μ (alignmentOriginalProductFaceFailure D (alignmentGeometryWithGap F i gap) q₀ w T d shift slots weight g a B L c C ε e j) ≤
      event μ (fun y => E0 y ∨ E1 y) := by
    apply event_mono_on_support μ _ _ hm
    intro y hy hbad
    by_contra hn
    have hn0 : ¬ E0 y := fun h => hn (Or.inl h)
    have hn1 : ¬ E1 y := fun h => hn (Or.inr h)
    have hyr := conditionMass_support _ _ hy
    have hykey : alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T x=alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T y := by
      by_contra hneq
      have hnz := Finsupp.mem_support_iff.mp hy
      have hneq' : ¬ alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T y=alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T x :=
        fun h => hneq h.symm
      rw [conditionMass_apply,if_neg hneq'] at hnz
      exact hnz rfl
    obtain ⟨lower,upper,ellResidue,obs,hbox,hobs,hlarge⟩ := hbad
    let p := alignmentMicrocellFirst (alignedSqrtMicrocellWidth ((alignmentGeometryWithGap F i gap).gap w i.val) (F.modulus w)) (F.modulus w) (y i)
    let Y : ℤ := (alignmentShortBinStart (alignmentGeometryWithGap F i gap) w i T x : ℤ)/(F.modulus w : ℤ)
    let choice := alignmentDenominatorChoice (alignmentDenominatorRemainder d hd
      (fun z : Option κ => alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct y T) p Y z (ellResidue z)))
    let lo := fun z => alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct y T) p Y z ⌈lower z⌉
    let hi := fun z => alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct y T) p Y z ⌈upper z⌉
    let O0 := alignmentOriginalProductCubeMean D (alignmentGeometryWithGap F i gap) q₀ w T y p d ellResidue lower upper shift slots weight g a (fun ν => obs ν)
    let O1 := alignmentOriginalProductCubeMean D (alignmentGeometryWithGap F i gap) q₀ w T y p d ellResidue lower upper shift faceSlots weight g a (fun ν => obs ν)
    let A0 := alignmentJointDenominatorSpatialMean D n v hv r b (alignmentGeometryWithGap F i gap) q₀ w T x d choice shift weight g a
      (fun k : T => y k.val) lo hi (alignmentJointNativeMetricProduct D n v hv slots obs)
    let A1 := alignmentJointDenominatorSpatialMean D n v hv r b (alignmentGeometryWithGap F i gap) q₀ w T x d choice shift weight g a
      (fun k : T => y k.val) lo hi (alignmentJointNativeMetricProduct D n v hv faceSlots obs)
    have hclose0 : ‖O0-A0‖ < ε/3 := by
      apply lt_of_not_ge
      intro h
      exact hn0 ⟨lower,upper,ellResidue,obs,hbox,hobs,h⟩
    have hclose1 : ‖O1-A1‖ < ε/3 := by
      apply lt_of_not_ge
      intro h
      exact hn1 ⟨lower,upper,ellResidue,obs,hbox,hobs,h⟩
    have hcloseT := hwt x y hx hykey hyr lower upper hbox e he j choice shift weight g a hegap obs hobs
    rw [←alignmentShortExposureKey_start_eq (alignmentGeometryWithGap F i gap) w i T hykey] at hcloseT
    have hcloseT' : ‖A1-A0‖ < ε/3 := hcloseT
    have htriangle : ‖O1-O0‖ ≤ ‖O1-A1‖+‖A1-A0‖+‖A0-O0‖ :=
      (norm_sub_le_norm_sub_add_norm_sub O1 A1 O0).trans (by linarith [norm_sub_le_norm_sub_add_norm_sub A1 A0 O0])
    rw [norm_sub_rev A0 O0] at htriangle
    change ε ≤ ‖O1-O0‖ at hlarge
    linarith
  have hbound := hinclude.trans (event_or_le_add μ E0 E1 hm)
  change event μ (alignmentOriginalProductFaceFailure D (alignmentGeometryWithGap F i gap) q₀ w T d shift slots weight g a B L c C ε e j) < δ
  linarith


end Hindman168
