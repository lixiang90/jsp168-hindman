import Hindman168.NativeNilmanifoldConstruction

/-! The genuine zero-dimensional native nilmanifold supplies the empty
recipe, so finite-family closure requires no external nonemptiness premise. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

noncomputable def trivialNativeNilmanifold (s : ℕ) : NativeNilmanifoldData.{u} s := by
  letI : LieGroup (𝓘(ℝ, PUnit.{u+1})) ∞ PUnit.{u+1} := {
    contMDiff_mul := by
      have he : (fun p : PUnit.{u+1} × PUnit.{u+1} => p.1 * p.2) = (fun _ => PUnit.unit) :=
        funext (fun _ => Subsingleton.elim _ _)
      rw [he]
      exact contMDiff_const
    contMDiff_inv := by
      have he : (fun p : PUnit.{u+1} => p⁻¹) = (fun _ => PUnit.unit) :=
        funext (fun _ => Subsingleton.elim _ _)
      rw [he]
      exact contMDiff_const }
  exact nativeNilmanifoldOfLie (E := PUnit.{u+1}) (H := PUnit.{u+1})
    (I := 𝓘(ℝ, PUnit.{u+1})) (G := PUnit.{u+1}) s
    (by rw [Group.nilpotencyClass_zero_iff_subsingleton.mpr inferInstance]; exact Nat.zero_le s) ⊤

end Hindman168
