import Hindman168.AlignmentJointIntegerSpatialSource
import Hindman168.SelectedAlignmentJointSourceTransportIntegerVector

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


theorem selected_alignment_joint_exposed_integer_spatial_native_source
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F) (gap : ℕ)
    {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀+1 ≤ w)
    (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i) {x y : Fin N → ℕ}
    (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hkey : alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T x=alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T y)
    (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ)
    (g a : ∀ ν, (D ν).G) (spatial : Option κ → ℤ) :
    alignmentJointExposedNativeSource D n v hv r b (alignmentGeometryWithGap F i.val gap) q₀ w T x shift weight g a
      (Sum.elim (fun j => (spatial j : ℝ)) (fun j => (y j : ℝ)))=
      nativeFinitePiGroupValue (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
        (fun ν => alignmentNativeIntegerSpatialArray (D ν) (n ν) (v ν) (hv ν)
          (alignmentGeometryWithGap F i.val gap) q₀ w T y (shift ν) (weight ν) (g ν) (a ν) spatial) := by
  apply native_finite_pi_vector_source_samples
  intro ν
  exact selected_alignment_exposed_integer_spatial_native_vector_eval (D ν) (n ν) (v ν) (hv ν) (b ν)
    hF gap hq hw T hT x y hx hy hkey (shift ν) (weight ν) (g ν) (a ν) spatial

theorem selected_alignment_joint_tail_integer_spatial_native_source
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F) (gap : ℕ)
    {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀+1 ≤ w)
    (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i) {x y : Fin N → ℕ}
    (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hkey : alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T x=alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T y)
    (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ)
    (g a : ∀ ν, (D ν).G) (spatial : Option κ → ℤ) :
    alignmentJointTailSpatialSource D n v hv r b (alignmentGeometryWithGap F i.val gap) q₀ w T x shift weight g a
      (fun k : T => y k.val) (fun j => (spatial j : ℝ))=
      nativeFinitePiGroupValue (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
        (fun ν => alignmentNativeIntegerSpatialArray (D ν) (n ν) (v ν) (hv ν)
          (alignmentGeometryWithGap F i.val gap) q₀ w T y (shift ν) (weight ν) (g ν) (a ν) spatial) := by
  unfold alignmentJointTailSpatialSource
  rw [alignment_joint_exposed_native_source_tail_congr D n v hv r b (alignmentGeometryWithGap F i.val gap) q₀ w T x
    shift weight g a (fun j => (spatial j : ℝ))
    (fun k => (alignmentTailTuple T x (fun k : T => y k.val) k : ℝ)) (fun k => (y k : ℝ))
    (by
      intro k hk
      exact congrArg (fun z : ℕ => (z : ℝ))
        (alignment_tail_tuple_inside T x (fun k : T => y k.val) (⟨k,hk⟩ : T)))]
  exact selected_alignment_joint_exposed_integer_spatial_native_source D n v hv r b
    hF gap hq hw T hT hx hy hkey shift weight g a spatial


end Hindman168
