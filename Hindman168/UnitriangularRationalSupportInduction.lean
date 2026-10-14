import Hindman168.UnitriangularSupportLatticeReduction
import Mathlib.Data.Nat.Find
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! A nonzero actual strict matrix Lie subalgebra has a shallowest nonzero
support layer. The layer is chosen by the first failed depth containment,
not supplied as an adapted-coordinate hypothesis. A nonzero coordinate on
that layer cuts out a rational admissible slice of strictly smaller real
dimension. These facts supply a terminating induction for genuine lattice
representative construction. -/

noncomputable section
namespace Hindman168
open Matrix Submodule Set Module

variable {n : ℕ}
local instance supportInductionMatrixLieRing : LieRing (Matrix (Fin n) (Fin n) ℝ) :=
  LieRing.ofAssociativeRing

 theorem unitriangularLieSubalgebra_first_support
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n ℝ)
    (hV0 : V.toSubmodule ≠ ⊥) :
    ∃ k : ℕ, 1 ≤ k ∧ V ≤ matrixDepthLieSubalgebra n k ℝ ∧
      ∃ X ∈ V, ∃ a b : Fin n, b.val = a.val + k ∧ X a b ≠ 0 := by
  classical
  have hX : ∃ X ∈ V, X ≠ 0 := by
    by_contra h
    push Not at h
    apply hV0
    apply bot_unique
    intro X hx
    change X = 0
    exact h X hx
  obtain ⟨X, hX, hX0⟩ := hX
  have hex : ∃ s : ℕ, ¬V ≤ matrixDepthLieSubalgebra n s ℝ := by
    refine ⟨n, ?_⟩
    intro hs
    exact hX0 (MatrixDepth.eq_zero (hs hX) le_rfl)
  let s := Nat.find hex
  have hbad : ¬V ≤ matrixDepthLieSubalgebra n s ℝ := Nat.find_spec hex
  have hs : 2 ≤ s := by
    by_contra h
    have hle : V ≤ matrixDepthLieSubalgebra n s ℝ := by
      intro A hA
      exact MatrixDepth.antitone (hV hA) (by omega)
    exact hbad hle
  have hprev : V ≤ matrixDepthLieSubalgebra n (s - 1) ℝ := by
    exact not_not.mp (Nat.find_min hex (by dsimp [s]; omega))
  have hentry : ∃ A ∈ V, ∃ a b : Fin n, b.val < a.val + s ∧ A a b ≠ 0 := by
    by_contra h
    push Not at h
    apply hbad
    intro A hA a b hab
    exact h A hA a b hab
  obtain ⟨A, hA, a, b, hab, hneq⟩ := hentry
  have hgap : a.val + (s - 1) ≤ b.val := by
    by_contra hg
    exact hneq (hprev hA a b (by omega))
  refine ⟨s - 1, by omega, hprev, A, hA, a, b, ?_, hneq⟩
  omega

 theorem unitriangularLieSubalgebra_false_support_slice
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
    (k : ℕ) (hk : 1 ≤ k) (hdepth : V ≤ matrixDepthLieSubalgebra n k ℝ) :
    V ⊓ matrixSupportSliceLieSubalgebra n k ℝ hk (fun _ _ => False)
      (by intro i j h; exact False.elim h) = V := by
  apply inf_eq_left.mpr
  intro A hA
  exact ⟨hdepth hA, fun _ _ h => False.elim h⟩

 theorem unitriangularLieSubalgebra_pivot_slice_finrank_lt
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
    (k : ℕ) (hk : 1 ≤ k) (a b : Fin n) (hab : b.val < a.val + k + 1)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : X ∈ V) (hneq : X a b ≠ 0) :
    finrank ℝ (V ⊓ matrixSupportSliceLieSubalgebra n k ℝ hk
      (fun i j => i = a ∧ j = b)
      (by intro i j h; rcases h with ⟨rfl, rfl⟩; exact hab)).toSubmodule <
      finrank ℝ V.toSubmodule := by
  apply Submodule.finrank_lt_finrank_of_lt
  apply lt_of_le_of_ne inf_le_left
  intro heq
  have hm : X ∈ V.toSubmodule ⊓ (matrixSupportSliceLieSubalgebra n k ℝ hk
      (fun i j => i = a ∧ j = b)
      (by intro i j h; rcases h with ⟨rfl, rfl⟩; exact hab)).toSubmodule := by
    rw [heq]
    exact hX
  exact hneq (hm.2.2 a b ⟨rfl, rfl⟩)

end Hindman168
