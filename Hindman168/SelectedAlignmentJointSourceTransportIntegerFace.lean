import Hindman168.AlignmentJointIntegerFaceTranslation
import Hindman168.SelectedAlignmentJointSourceTransportIntegerJoint

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


theorem selected_alignment_joint_tail_integer_spatial_own_pair_translation
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F) (gap : ℕ)
    {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀+1 ≤ w)
    (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i) {x y : Fin N → ℕ}
    (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hkey : alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T x=alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T y)
    (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ)
    (g a : ∀ ν, (D ν).G) (spatial : Option κ → ℤ)
    (j : κ) (e : AlignmentAddingPair N i) (he : e.targetTail=T) :
    alignmentJointNativeSlotTranslation D n v hv (fun ν => Pi.single e (weight ν j))
      (alignmentJointTailSpatialSource D n v hv r b (alignmentGeometryWithGap F i.val gap) q₀ w T x shift weight g a
        (fun k : T => y k.val) (fun k => (spatial k : ℝ)))=
      alignmentJointTailSpatialSource D n v hv r b (alignmentGeometryWithGap F i.val gap) q₀ w T x shift weight g a
        (fun k : T => y k.val)
        (fun k => ((spatial k+if k=some j then alignmentPairProgression q₀ w (F.modulus w) e y else 0 : ℤ) : ℝ)) := by
  rw [selected_alignment_joint_tail_integer_spatial_native_source D n v hv r b hF gap hq hw T hT hx hy hkey,
    selected_alignment_joint_tail_integer_spatial_native_source D n v hv r b hF gap hq hw T hT hx hy hkey]
  apply (nativeFinitePiGroupEquiv (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).injective
  funext ν
  exact alignment_integer_spatial_array_own_pair_translation (D ν) (n ν) (v ν) (hv ν)
    (alignmentGeometryWithGap F i.val gap) q₀ w T y (shift ν) (weight ν) (g ν) (a ν) spatial j e he

theorem selected_alignment_joint_tail_integer_coset_own_pair_translation
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F) (gap : ℕ)
    {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀+1 ≤ w)
    (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i) {x y : Fin N → ℕ}
    (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hkey : alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T x=alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T y)
    (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ)
    (g a : ∀ ν, (D ν).G) (spatial : Option κ → ℤ)
    (j : κ) (e : AlignmentAddingPair N i) (he : e.targetTail=T) :
    alignmentJointNativeCosetSlotTranslation D n v hv (fun ν => Pi.single e (weight ν j))
      (QuotientGroup.mk (alignmentJointTailSpatialSource D n v hv r b (alignmentGeometryWithGap F i.val gap) q₀ w T x shift weight g a
        (fun k : T => y k.val) (fun k => (spatial k : ℝ))))=
      QuotientGroup.mk (alignmentJointTailSpatialSource D n v hv r b (alignmentGeometryWithGap F i.val gap) q₀ w T x shift weight g a
        (fun k : T => y k.val)
        (fun k => ((spatial k+if k=some j then alignmentPairProgression q₀ w (F.modulus w) e y else 0 : ℤ) : ℝ))) := by
  rw [alignment_joint_native_coset_slot_translation_mk,
    selected_alignment_joint_tail_integer_spatial_own_pair_translation D n v hv r b hF gap hq hw T hT hx hy hkey
      shift weight g a spatial j e he]


end Hindman168
