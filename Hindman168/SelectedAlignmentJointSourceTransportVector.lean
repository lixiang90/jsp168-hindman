import Hindman168.AlignmentExposedNativeVectorPolynomial
import Hindman168.SelectedAlignmentJointSourceTransportLog

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
  {r : ℕ} (b : Basis (Fin r) ℝ (alignmentNativeArrayData D n v hv).E)

theorem selected_alignment_exposed_native_vector_polynomial_frozen
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F) (gap : ℕ)
    (q₀ w : ℕ) (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i) {x y : Fin N → ℕ}
    (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hkey : alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T x=alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T y)
    (shift : AlignmentAddingPair N i → ℤ) (weight : κ → ℤ) (g a : D.G) :
    alignmentExposedNativeVectorPolynomial D n v hv b (alignmentGeometryWithGap F i.val gap) q₀ w T y shift weight g a =
      alignmentExposedNativeVectorPolynomial D n v hv b (alignmentGeometryWithGap F i.val gap) q₀ w T x shift weight g a := by
  unfold alignmentExposedNativeVectorPolynomial
  apply congrArg (roughVectorMvFromBasis b)
  funext j
  exact selected_alignmentNativeExposedJointLogPolynomial_frozen (E := D.E) (I := D.I) (G := D.G)
    (κ := κ) (N := N) (i := i) n v hF gap q₀ w T hT hx hy hkey
    shift weight g a _

theorem selected_alignment_exposed_native_vector_polynomial_actual_eval
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F) (gap : ℕ)
    {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀+1 ≤ w)
    (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i) {x y : Fin N → ℕ}
    (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hkey : alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T x=alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T y)
    (p ell : ℤ) (hp : Int.ModEq (F.modulus w : ℕ) p (y i))
    (inc weight : κ → ℤ) (shift : AlignmentAddingPair N i → ℤ) (g a : D.G) :
    let Y : ℤ := (alignmentShortBinStart (alignmentGeometryWithGap F i.val gap) w i T x : ℤ)/(F.modulus w : ℤ)
    let tau : ℤ := alignmentNaturalBlockProduct y T
    let z := Sum.elim
      (fun j : Option κ => match j with
        | none => (alignmentCubeBase (F.modulus w) tau p Y ell : ℝ)
        | some j => ((tau*inc j : ℤ) : ℝ)) (fun j : Fin N => (y j : ℝ))
    let actual := alignmentNativeArrayDataValue D n v hv (alignmentNativeCanonicalCubeArray n v hv g a y (F.modulus w)
      (fun e => alignmentPairResidue q₀ w (F.modulus w) e y)
      (fun e => alignmentPairProgression q₀ w (F.modulus w) e y)
      T p Y ell inc weight shift)
    roughVectorMvEval (alignmentExposedNativeVectorPolynomial D n v hv b (alignmentGeometryWithGap F i.val gap) q₀ w T x shift weight g a) z =
      nativeLieGlobalLogarithm (E := (alignmentNativeArrayData D n v hv).E)
        (I := (alignmentNativeArrayData D n v hv).I) (G := (alignmentNativeArrayData D n v hv).G) actual := by
  dsimp only
  rw [alignmentExposedNativeVectorPolynomial,roughVectorMvFromBasis_eval]
  have hcoordinates (j : Fin r) := selected_alignmentNativeExposedJointLogPolynomial_eval
    (E := D.E) (I := D.I) (G := D.G) (κ := κ) (N := N) (i := i) n v hv
    hF gap hq hw T hT hx hy hkey p ell hp inc weight shift g a
    ((b.coord j).comp (alignmentNativeArrayDataCoefficients D n v hv).symm.toLinearMap)
  dsimp only at hcoordinates
  let actual := alignmentNativeArrayDataValue D n v hv (alignmentNativeCanonicalCubeArray n v hv g a y (F.modulus w)
      (fun e => alignmentPairResidue q₀ w (F.modulus w) e y)
      (fun e => alignmentPairProgression q₀ w (F.modulus w) e y)
      T p ((alignmentShortBinStart (alignmentGeometryWithGap F i.val gap) w i T x : ℤ)/(F.modulus w : ℤ)) ell inc weight shift)
  have hc := alignment_array_data_coefficient_log D n v hv actual
  have hcoords (j : Fin r) :
      MvPolynomial.eval (Sum.elim
        (fun z : Option κ => match z with
          | none => (alignmentCubeBase (F.modulus w) (alignmentNaturalBlockProduct y T) p
              ((alignmentShortBinStart (alignmentGeometryWithGap F i.val gap) w i T x : ℤ)/(F.modulus w : ℤ)) ell : ℝ)
          | some z => (((alignmentNaturalBlockProduct y T : ℤ)*inc z : ℤ) : ℝ))
        (fun z : Fin N => (y z : ℝ)))
        (alignmentNativeExposedJointLogPolynomial n v (alignmentGeometryWithGap F i.val gap) q₀ w T x shift weight g a
          ((b.coord j).comp (alignmentNativeArrayDataCoefficients D n v hv).symm.toLinearMap)) =
      b.coord j (nativeLieGlobalLogarithm (E := (alignmentNativeArrayData D n v hv).E)
        (I := (alignmentNativeArrayData D n v hv).I) (G := (alignmentNativeArrayData D n v hv).G) actual) := by
    have hh := (hcoordinates j).trans (congrArg
      ((b.coord j).comp (alignmentNativeArrayDataCoefficients D n v hv).symm.toLinearMap) hc.symm)
    simp only [LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,LinearEquiv.symm_apply_apply] at hh
    (convert hh using 1; congr! 8)
  simp_rw [hcoords]
  exact b.sum_repr _


end Hindman168
