import Hindman168.AlignmentJointSourceTailDependence
import Hindman168.AlignmentTailRestTuple

/-! Genuine ALL-REAL source restriction identity. Each removed-factor source,
when its parameter is set to the actual factor, is the SAME full joint spatial
source. This identifies every term in the literal factor-removal telescope. -/
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

theorem alignment_joint_removed_native_source_restriction
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (j : Fin N) (frozen : Fin N → ℝ)
    (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G)
    (z : ℝ) (spatial : Option κ → ℝ) :
    alignmentJointRemovedNativeSource D n v hv r b F q₀ w T x j frozen shift weight g a
      (Option.elim · z spatial)=
    alignmentJointExposedNativeSource D n v hv r b F q₀ w T x shift weight g a
      (Sum.elim spatial (Function.update frozen j z)) := by
  unfold alignmentJointRemovedNativeSource alignmentJointExposedNativeSource nativeFinitePiVectorSource
  apply native_vector_polynomial_source_sample
  rw [native_vector_polynomial_source_log,alignmentJointRemovedNativePolynomial,
    rough_removed_factor_polynomial_eval]
  rfl

noncomputable def alignmentJointTailSpatialSource
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G)
    (tail : T → ℕ) :
    (Option κ → ℝ) → (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G :=
  fun spatial => alignmentJointExposedNativeSource D n v hv r b F q₀ w T x shift weight g a
    (Sum.elim spatial (fun k => (alignmentTailTuple T x tail k : ℝ)))

theorem alignment_joint_removed_native_actual_tail_spatial_source
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (j : T) (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ)
    (g a : ∀ ν, (D ν).G) (tail : T → ℕ) (spatial : Option κ → ℝ) :
    alignmentJointRemovedNativeSource D n v hv r b F q₀ w T x j.val
      (fun k => (alignmentTailTuple T x tail k : ℝ)) shift weight g a
      (Option.elim · (tail j : ℝ) spatial)=
    alignmentJointTailSpatialSource D n v hv r b F q₀ w T x shift weight g a tail spatial := by
  rw [alignment_joint_removed_native_source_restriction]
  have hv : (tail j : ℝ)=(alignmentTailTuple T x tail j.val : ℝ) :=
    congrArg (fun n : ℕ => (n : ℝ)) (alignment_tail_tuple_inside T x tail j).symm
  rw [hv,Function.update_eq_self]
  rfl

end Hindman168
