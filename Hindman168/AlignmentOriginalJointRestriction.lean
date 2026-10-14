import Hindman168.AlignmentOriginalJointRealSource
import Hindman168.NativeFinitePiCosetRestriction

/-! Restricting the FULL heterogeneous original source gives precisely the
original subfamily source at every integer sample. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] alignmentAddingPairFintype lieGroup_smooth_min_three

variable {ι κ : Type} [Fintype ι] [Fintype κ] {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))

theorem alignment_original_joint_point_restriction (select : κ → ι)
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : ι → Finset (Fin N))
    (y : Fin N → ℕ) (p : ℤ) (shift : ι → AlignmentAddingPair N i → ℤ)
    (g a : ∀ ν, (D ν).G) (z : ℤ) :
    nativeFinitePiCosetRestriction (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) select
      (alignmentOriginalJointPointOrbit D n v hv F q₀ w T y p shift g a z : (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G ⧸ (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ) =
      (QuotientGroup.mk (alignmentOriginalJointPointOrbit (D ∘ select) (n ∘ select) (fun k => v (select k)) (fun k => hv (select k)) F q₀ w (T ∘ select) y p
        (fun k => shift (select k)) (fun k => g (select k)) (fun k => a (select k)) z) : (nativeFinitePiData (fun k => alignmentNativeArrayData (D (select k)) (n (select k)) (v (select k)) (hv (select k)))).G ⧸ (nativeFinitePiData (fun k => alignmentNativeArrayData (D (select k)) (n (select k)) (v (select k)) (hv (select k)))).Γ) := by
  apply (nativeFinitePiCosetHomeomorph _).injective
  funext k
  simp only [native_finite_pi_coset_homeomorph_apply,native_finite_pi_restriction_coordinate,
    native_finite_pi_coset_coordinate_mk,alignment_original_joint_point_orbit_component,Function.comp_apply]

theorem alignment_original_joint_real_restriction_integer (select : κ → ι)
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : ι → Finset (Fin N))
    (y : Fin N → ℕ) (p : ℤ) (shift : ι → AlignmentAddingPair N i → ℤ)
    (g a : ∀ ν, (D ν).G) (z : ℤ) :
    nativeFinitePiCosetRestriction (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) select
      (alignmentOriginalJointRealSource D n v hv F q₀ w T y p shift g a (z : ℝ) : (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G ⧸ (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ) =
      (QuotientGroup.mk (alignmentOriginalJointRealSource (D ∘ select) (n ∘ select) (fun k => v (select k)) (fun k => hv (select k)) F q₀ w (T ∘ select) y p
        (fun k => shift (select k)) (fun k => g (select k)) (fun k => a (select k)) (z : ℝ)) : (nativeFinitePiData (fun k => alignmentNativeArrayData (D (select k)) (n (select k)) (v (select k)) (hv (select k)))).G ⧸ (nativeFinitePiData (fun k => alignmentNativeArrayData (D (select k)) (n (select k)) (v (select k)) (hv (select k)))).Γ) := by
  rw [alignment_original_joint_real_source_integer,alignment_original_joint_real_source_integer]
  exact alignment_original_joint_point_restriction D n v hv select F q₀ w T y p shift g a z

end Hindman168
