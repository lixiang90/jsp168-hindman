import Hindman168.AlignmentJointTerminalFaceProducts
import Hindman168.SelectedAlignmentJointSourceTransportFaceMean

/-! Gap-view adapters for the repository's original native source proofs.
The original master conditions and modulus are retained; only the short
exposure key and its bin origin use the separately specified model gap.
No master conditions for the changed-gap view are asserted. -/
namespace Hindman168
open Module
open scoped Manifold ContDiff BigOperators Classical
universe u


variable {ι : Type} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))
  (r : ι → ℕ) (b : ∀ ν, Basis (Fin (r ν)) ℝ (alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)).E)


theorem selected_alignment_joint_terminal_product_face_mean
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F) (gap : ℕ)
    {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀+1 ≤ w)
    (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i) {x y : Fin N → ℕ}
    (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hkey : alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T x=alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T y)
    (d : ℕ) (choice lo hi : Option κ → ℤ)
    (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ)
    (g a : ∀ ν, (D ν).G) (j : κ) (e : AlignmentAddingPair N i) (he : e.targetTail=T)
    (slots : ι → AlignmentAddingPair N i → ℤ) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    ∀ obs : ∀ ν, C((D ν).G ⧸ (D ν).Γ,ℂ),
      alignmentJointTranslatedDenominatorMean D n v hv r b (alignmentGeometryWithGap F i.val gap) q₀ w T x d choice shift weight g a
        (fun k : T => y k.val) lo hi
        (fun k => if k=some j then alignmentPairProgression q₀ w (F.modulus w) e y else 0)
        (alignmentJointNativeMetricProduct D n v hv slots obs)=
      alignmentJointDenominatorSpatialMean D n v hv r b (alignmentGeometryWithGap F i.val gap) q₀ w T x d choice shift weight g a
        (fun k : T => y k.val) lo hi
        (alignmentJointNativeMetricProduct D n v hv (fun ν => slots ν+Pi.single e (weight ν j)) obs) := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  intro obs
  rw [selected_alignment_joint_terminal_denominator_face_mean D n v hv r b hF gap hq hw T hT hx hy hkey
    d choice lo hi shift weight g a j e he (alignmentJointNativeMetricProduct D n v hv slots obs)]
  congr 1
  funext z
  exact congrArg (fun f : C(J.G ⧸ J.Γ,ℂ) => f z)
    (alignment_joint_native_translated_metric_product_eq D n v hv slots
      (fun ν => Pi.single e (weight ν j)) obs)


end Hindman168
