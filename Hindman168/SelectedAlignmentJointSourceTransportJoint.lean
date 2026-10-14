import Hindman168.AlignmentJointExposedNativeSource
import Hindman168.SelectedAlignmentJointSourceTransportVector

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

theorem selected_alignment_joint_exposed_native_polynomial_frozen
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F) (gap : ℕ)
    (q₀ w : ℕ) (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i) {x y : Fin N → ℕ}
    (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hkey : alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T x=alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T y)
    (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G) :
    alignmentJointExposedNativePolynomial D n v hv r b (alignmentGeometryWithGap F i.val gap) q₀ w T y shift weight g a =
      alignmentJointExposedNativePolynomial D n v hv r b (alignmentGeometryWithGap F i.val gap) q₀ w T x shift weight g a := by
  unfold alignmentJointExposedNativePolynomial
  apply congrArg (nativeFinitePiVectorPolynomial (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)))
  funext ν
  exact selected_alignment_exposed_native_vector_polynomial_frozen (D ν) (n ν) (v ν) (hv ν) (b ν)
    hF gap q₀ w T hT hx hy hkey (shift ν) (weight ν) (g ν) (a ν)

theorem selected_alignment_joint_exposed_native_source_actual_sample
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F) (gap : ℕ)
    {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀+1 ≤ w)
    (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i) {x y : Fin N → ℕ}
    (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hkey : alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T x=alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T y)
    (p ell : ℤ) (hp : Int.ModEq (F.modulus w : ℕ) p (y i))
    (inc : κ → ℤ) (weight : ι → κ → ℤ) (shift : ι → AlignmentAddingPair N i → ℤ)
    (g a : ∀ ν, (D ν).G) :
    let Y : ℤ := (alignmentShortBinStart (alignmentGeometryWithGap F i.val gap) w i T x : ℤ)/(F.modulus w : ℤ)
    let tau : ℤ := alignmentNaturalBlockProduct y T
    let z := Sum.elim
      (fun j : Option κ => match j with
        | none => (alignmentCubeBase (F.modulus w) tau p Y ell : ℝ)
        | some j => ((tau*inc j : ℤ) : ℝ)) (fun j : Fin N => (y j : ℝ))
    let actual := fun ν => alignmentNativeArrayDataValue (D ν) (n ν) (v ν) (hv ν)
      (alignmentNativeCanonicalCubeArray (n ν) (v ν) (hv ν) (g ν) (a ν) y (F.modulus w)
        (fun e => alignmentPairResidue q₀ w (F.modulus w) e y)
        (fun e => alignmentPairProgression q₀ w (F.modulus w) e y)
        T p Y ell inc (weight ν) (shift ν))
    alignmentJointExposedNativeSource D n v hv r b (alignmentGeometryWithGap F i.val gap) q₀ w T x shift weight g a z =
      nativeFinitePiGroupValue (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) actual := by
  dsimp only
  apply native_finite_pi_vector_source_samples
  intro ν
  exact selected_alignment_exposed_native_vector_polynomial_actual_eval (D ν) (n ν) (v ν) (hv ν) (b ν)
    hF gap hq hw T hT hx hy hkey p ell hp inc (weight ν) (shift ν) (g ν) (a ν)


end Hindman168
