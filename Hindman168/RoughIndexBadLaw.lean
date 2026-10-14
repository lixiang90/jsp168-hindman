import Hindman168.RoughNativeBadIndex

/-! Exact equality of the original existential bad-event laws under the
literal parameter change. All varying boxes/residues/tests are retained. -/
namespace Hindman168
universe u

theorem rough_index_bad_affine_iff {κ : Type*} [Fintype κ] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (Q : (Option κ → ℝ) → D.G)
    (a b z t : ℕ) (Z c C : ℝ) (L : NNReal) (B η : ℝ) :
    RoughNativeBadIndex D (fun x => Q
      (Option.elim · ((a : ℝ)+(b : ℝ)*x none) (fun j => x (some j))))
      z t Z c C L B η ↔ RoughNativeBadIndex D Q (a+b*z) t Z c C L B η := by
  unfold RoughNativeBadIndex
  simp only [Option.elim_none,Option.elim_some,Nat.cast_add,Nat.cast_mul]

end Hindman168
