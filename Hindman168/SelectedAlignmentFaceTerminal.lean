import Hindman168.AlignmentJointTerminalFaceProducts
import Hindman168.SelectedAlignmentJointSourceTransportFaceProduct
import Hindman168.SelectedAlignmentBoxRemovalChoices
import Hindman168.SelectedAlignmentTerminalTranslation

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

theorem selected_alignment_joint_actual_terminal_product_face_eventually
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F) (gap : Fin N) (hgap : gap ≤ i)
    (q₀ : ℕ) (hq : 0 < q₀) (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < gap) (d : ℕ) (hd : 0 < d)
    (c C : ℝ) (Kbox : ℕ) (hc : 0 < c) (hC : 0 ≤ C) (hKbox : C+1 ≤ (Kbox : ℝ))
    (slots : ι → AlignmentAddingPair N i → ℤ) (B : ι → ℝ) (L : ι → NNReal) (hB : ∀ ν, 0 ≤ B ν)
    {ε : ℝ} (hε : 0 < ε) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    ∀ᶠ w in atTop, ∀ x y : Fin N → ℕ,
      x ∈ (globalRawMass (F.cutoff w) (primorial w) N).support →
      alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T x=alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T y →
      y ∈ (globalRawMass (F.cutoff w) (primorial w) N).support →
      ∀ lower upper : Option κ → ℝ,
      (∀ z, |lower z| ≤ C*alignmentLocalLength (alignmentGeometryWithGap F i gap) w i ∧ |upper z| ≤ C*alignmentLocalLength (alignmentGeometryWithGap F i gap) w i ∧
        c*alignmentLocalLength (alignmentGeometryWithGap F i gap) w i ≤ upper z-lower z) →
      ∀ (e : AlignmentAddingPair N i) (_he : e.targetTail=T) (coordinate : κ) (choice : Option κ → ℤ)
        (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G), e.sourcePivot < gap →
      let p := alignmentMicrocellFirst (alignedSqrtMicrocellWidth ((alignmentGeometryWithGap F i gap).gap w i.val) (F.modulus w)) (F.modulus w) (y i)
      let Y : ℤ := (alignmentShortBinStart (alignmentGeometryWithGap F i gap) w i T y : ℤ)/(F.modulus w : ℤ)
      let lo := fun z => alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct y T) p Y z ⌈lower z⌉
      let hi := fun z => alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct y T) p Y z ⌈upper z⌉
      ∀ obs : ∀ ν, C((D ν).G ⧸ (D ν).Γ,ℂ),
      (∀ ν, obs ν ∈ boundedComplexLipschitzObservables ((D ν).G ⧸ (D ν).Γ) (B ν) (L ν)) →
      ‖alignmentJointDenominatorSpatialMean D n v hv r b (alignmentGeometryWithGap F i gap) q₀ w T x d choice shift weight g a
          (fun k : T => y k.val) lo hi
          (alignmentJointNativeMetricProduct D n v hv (fun ν => slots ν+Pi.single e (weight ν coordinate)) obs)-
        alignmentJointDenominatorSpatialMean D n v hv r b (alignmentGeometryWithGap F i gap) q₀ w T x d choice shift weight g a
          (fun k : T => y k.val) lo hi (alignmentJointNativeMetricProduct D n v hv slots obs)‖ < ε := by
  have hTi : ∀ j ∈ T, j < i := fun j hj => (hT j hj).trans_le hgap
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  have hh := selected_alignment_joint_actual_terminal_translation_eventually (κ := κ) D n v hv r b
    hF gap q₀ hq T d hd c C Kbox hc hC hKbox slots B L hB hε
  filter_upwards [hh,eventually_ge_atTop (q₀+1)] with w hw hwq
  intro x y hx hkey hy lower upper hbox e he coordinate choice shift weight g a hegap obs hobs
  have hbound := hw x y hy lower upper hbox e (some coordinate) choice shift weight g a hegap
    (alignmentJointNativeMetricProduct D n v hv slots obs) ⟨obs,(fun ν _ => hobs ν),rfl⟩
  rw [selected_alignment_joint_terminal_product_face_mean D n v hv r b hF gap.val hq hwq T hTi
    (alignmentGlobalRawMass_support_coprime (alignmentGeometryWithGap F i gap) w x hx) (alignmentGlobalRawMass_support_coprime (alignmentGeometryWithGap F i gap) w y hy)
    hkey d choice _ _ shift weight g a coordinate e he slots obs] at hbound
  exact hbound


end Hindman168
