import Hindman168.AlignmentNativeIntegerSpatialArray
import Hindman168.SelectedAlignmentJointSourceTransportIntegerParameters

/-! Gap-view adapters for the repository's original native source proofs.
The original master conditions and modulus are retained; only the short
exposure key and its bin origin use the separately specified model gap.
No master conditions for the changed-gap view are asserted. -/
namespace Hindman168
open Module
open scoped Manifold ContDiff BigOperators Classical
universe u


variable {κ : Type*} [Fintype κ] {N : ℕ} {i : Fin N} {s : ℕ}
  (D : NativeNilmanifoldData.{u} s) (n : ℕ)
  (v : Fin (n+1) → AlignmentAddingPair N i → ℤ)
  (hv : Function.Injective (alignmentNativeFiniteEvaluation (E := D.E) (I := D.I) (G := D.G) n v))
  {r : ℕ} (basis : Basis (Fin r) ℝ (alignmentNativeArrayData D n v hv).E)

theorem selected_alignment_exposed_integer_spatial_native_vector_eval
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F) (gap : ℕ)
    {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀+1 ≤ w) (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i)
    (x y : Fin N → ℕ) (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hkey : alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T x=alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T y)
    (shift : AlignmentAddingPair N i → ℤ) (weight : κ → ℤ) (g basepoint : D.G) (spatial : Option κ → ℤ) :
    roughVectorMvEval (alignmentExposedNativeVectorPolynomial D n v hv basis (alignmentGeometryWithGap F i.val gap) q₀ w T x shift weight g basepoint)
      (Sum.elim (fun j => (spatial j : ℝ)) (fun j => (y j : ℝ)))=
    nativeLieGlobalLogarithm (E := (alignmentNativeArrayData D n v hv).E)
      (I := (alignmentNativeArrayData D n v hv).I) (G := (alignmentNativeArrayData D n v hv).G)
      (alignmentNativeIntegerSpatialArray D n v hv (alignmentGeometryWithGap F i.val gap) q₀ w T y shift weight g basepoint spatial) := by
  letI := alignmentAddingPairFintype N i
  letI : LieGroup D.I (minSmoothness ℝ 3) D.G := lieGroup_smooth_min_three
  let actual := alignmentNativeIntegerSpatialArray D n v hv (alignmentGeometryWithGap F i.val gap) q₀ w T y shift weight g basepoint spatial
  have hc := alignment_array_data_coefficient_log D n v hv actual
  have hp := selected_alignment_exposed_integer_spatial_base_eval hF gap q₀ w i T hT x y hx hy hkey shift weight spatial
  have hqeval (e : AlignmentAddingPair N i) := selected_alignmentExposedJointIncrementPolynomial_eval hF gap hq hw i T hx hy hkey
    (fun j => (spatial j : ℝ)) e
  have hcoord (j : Fin r) :
      MvPolynomial.eval (Sum.elim (fun k => (spatial k : ℝ)) (fun k => (y k : ℝ)))
        (alignmentNativeExposedJointLogPolynomial n v (alignmentGeometryWithGap F i.val gap) q₀ w T x shift weight g basepoint
          ((basis.coord j).comp (alignmentNativeArrayDataCoefficients D n v hv).symm.toLinearMap))=
      basis.coord j (nativeLieGlobalLogarithm (E := (alignmentNativeArrayData D n v hv).E)
        (I := (alignmentNativeArrayData D n v hv).I) (G := (alignmentNativeArrayData D n v hv).G) actual) := by
    have he := alignmentNativeModelLogPolynomial_eval (E := D.E) (I := D.I) (G := D.G) n v hv g basepoint
      ((basis.coord j).comp (alignmentNativeArrayDataCoefficients D n v hv).symm.toLinearMap)
      (alignmentExposedJointBasePolynomial (alignmentGeometryWithGap F i.val gap) q₀ w i T x shift weight)
      (alignmentExposedJointIncrementPolynomial (alignmentGeometryWithGap F i.val gap) q₀ w i T x)
      (Sum.elim (fun k => (spatial k : ℝ)) (fun k => (y k : ℝ)))
      (alignmentIntegerSpatialBase (alignmentGeometryWithGap F i.val gap) q₀ w i T y shift weight spatial)
      (fun e => if e.targetTail=T then alignmentPairProgression q₀ w (F.modulus w) e y else 0) hp hqeval
    have hh := he.trans (congrArg
      ((basis.coord j).comp (alignmentNativeArrayDataCoefficients D n v hv).symm.toLinearMap) hc.symm)
    simp only [LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,LinearEquiv.symm_apply_apply] at hh
    exact hh
  rw [alignmentExposedNativeVectorPolynomial,roughVectorMvFromBasis_eval]
  simp_rw [hcoord]
  exact basis.sum_repr _


end Hindman168
