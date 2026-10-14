import Hindman168.NativeFinitePiCosetRestriction
import Hindman168.AlignmentOriginalJointRealSource

/-! Exact restriction of the original heterogeneous point orbit. Every
subfamily retains the original target, tail product, and sampled parameters.
The real source is restricted only at integers, using its proved identity
with the actual integer orbit. No interpolation hypothesis is introduced. -/
namespace Hindman168
open scoped Manifold ContDiff Classical
universe u

variable {ι κ : Type} [Fintype ι] [Fintype κ]
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν + 1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I)
      (G := (D ν).G) (n ν) (v ν))) (index : κ → ι)

theorem alignment_original_joint_point_orbit_restriction
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : ι → Finset (Fin N))
    (y : Fin N → ℕ) (p : ℤ) (shift : ι → AlignmentAddingPair N i → ℤ)
    (g a : ∀ ν, (D ν).G) (ell : ℤ) :
    nativeFinitePiGroupValue
      (fun k => alignmentNativeArrayData (D (index k)) (n (index k))
        (v (index k)) (hv (index k)))
      (fun k => nativeFinitePiGroupEquiv
        (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
        (alignmentOriginalJointPointOrbit D n v hv F q₀ w T y p shift g a ell)
        (index k)) =
      alignmentOriginalJointPointOrbit (D ∘ index) (n ∘ index)
        (fun k => v (index k)) (fun k => hv (index k))
        F q₀ w (T ∘ index) y p (shift ∘ index)
        (fun k => g (index k)) (fun k => a (index k)) ell := by
  rfl

theorem alignment_original_joint_real_source_integer_restriction
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : ι → Finset (Fin N))
    (y : Fin N → ℕ) (p : ℤ) (shift : ι → AlignmentAddingPair N i → ℤ)
    (g a : ∀ ν, (D ν).G) (ell : ℤ) :
    nativeFinitePiGroupValue
      (fun k => alignmentNativeArrayData (D (index k)) (n (index k))
        (v (index k)) (hv (index k)))
      (fun k => nativeFinitePiGroupEquiv
        (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
        (alignmentOriginalJointRealSource D n v hv F q₀ w T y p shift g a (ell : ℝ))
        (index k)) =
      alignmentOriginalJointRealSource (D ∘ index) (n ∘ index)
        (fun k => v (index k)) (fun k => hv (index k))
        F q₀ w (T ∘ index) y p (shift ∘ index)
        (fun k => g (index k)) (fun k => a (index k)) (ell : ℝ) := by
  rw [alignment_original_joint_real_source_integer,
    alignment_original_joint_real_source_integer]
  exact alignment_original_joint_point_orbit_restriction D n v hv index
    F q₀ w T y p shift g a ell

theorem alignment_original_joint_point_coset_restriction
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : ι → Finset (Fin N))
    (y : Fin N → ℕ) (p : ℤ) (shift : ι → AlignmentAddingPair N i → ℤ)
    (g a : ∀ ν, (D ν).G) (ell : ℤ) :
    nativeFinitePiCosetRestriction
      (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) index
      (QuotientGroup.mk
        (alignmentOriginalJointPointOrbit D n v hv F q₀ w T y p shift g a ell)) =
      QuotientGroup.mk (alignmentOriginalJointPointOrbit (D ∘ index) (n ∘ index)
        (fun k => v (index k)) (fun k => hv (index k))
        F q₀ w (T ∘ index) y p (shift ∘ index)
        (fun k => g (index k)) (fun k => a (index k)) ell) := by
  rw [native_finite_pi_coset_restriction_mk]
  exact congrArg QuotientGroup.mk
    (alignment_original_joint_point_orbit_restriction D n v hv index
      F q₀ w T y p shift g a ell)

theorem alignment_original_joint_real_coset_integer_restriction
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : ι → Finset (Fin N))
    (y : Fin N → ℕ) (p : ℤ) (shift : ι → AlignmentAddingPair N i → ℤ)
    (g a : ∀ ν, (D ν).G) (ell : ℤ) :
    nativeFinitePiCosetRestriction
      (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) index
      (QuotientGroup.mk
        (alignmentOriginalJointRealSource D n v hv F q₀ w T y p shift g a (ell : ℝ))) =
      QuotientGroup.mk (alignmentOriginalJointRealSource (D ∘ index) (n ∘ index)
        (fun k => v (index k)) (fun k => hv (index k))
        F q₀ w (T ∘ index) y p (shift ∘ index)
        (fun k => g (index k)) (fun k => a (index k)) (ell : ℝ)) := by
  rw [alignment_original_joint_real_source_integer,
    alignment_original_joint_real_source_integer]
  exact alignment_original_joint_point_coset_restriction D n v hv index
    F q₀ w T y p shift g a ell

end Hindman168
