import Hindman168.UnitriangularExponentialLattice
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Nilpotent

/-! The strict upper-triangular matrix Lie algebra uses the actual
associative matrix commutator. Its support layers are actual Lie ideals.
No Lie-group comparison or general BCH closure is assumed here. -/

namespace Hindman168
open Matrix

variable {n : ℕ} {R : Type*} [CommRing R]
local instance matrixLieRing : LieRing (Matrix (Fin n) (Fin n) R) := LieRing.ofAssociativeRing

 theorem MatrixDepth.lie {k l : ℕ} {A B : Matrix (Fin n) (Fin n) R}
    (hA : MatrixDepth k A) (hB : MatrixDepth l B) : MatrixDepth (k + l) ⁅A, B⁆ := by
  change MatrixDepth (k + l) (A * B - B * A)
  exact (hA.mul hB).sub (by simpa only [Nat.add_comm l k] using hB.mul hA)

 def strictUpperTriangularLieSubalgebra (n : ℕ) (R : Type*) [CommRing R] :
    LieSubalgebra R (Matrix (Fin n) (Fin n) R) where
  toSubmodule := StrictUpperTriangular n R
  lie_mem' hA hB := (hA.lie hB).antitone (by omega)

 abbrev UnitriangularLieAlgebra (n : ℕ) (R : Type*) [CommRing R] :=
  strictUpperTriangularLieSubalgebra n R

 theorem unitriangularLie_bracket_value (A B : UnitriangularLieAlgebra n R) :
    (⁅A, B⁆ : UnitriangularLieAlgebra n R).val = A.val * B.val - B.val * A.val := rfl

 def unitriangularLieDepth (n k : ℕ) (R : Type*) [CommRing R] :
    LieIdeal R (UnitriangularLieAlgebra n R) where
  carrier := {A | MatrixDepth k A.val}
  zero_mem' := matrixDepth_zero k
  add_mem' hA hB := hA.add hB
  smul_mem' c _ hA := hA.smul c
  lie_mem {A B} hB := (A.property.lie hB).antitone (by omega)

 theorem unitriangularLieDepth_bracket_le (k l : ℕ) :
    ⁅unitriangularLieDepth n k R, unitriangularLieDepth n l R⁆ ≤
      unitriangularLieDepth n (k + l) R := by
  rw [LieSubmodule.lie_le_iff]
  intro A hA B hB
  change MatrixDepth k A.val at hA
  change MatrixDepth l B.val at hB
  change MatrixDepth (k + l) (A.val * B.val - B.val * A.val)
  have hd := hA.lie hB
  change MatrixDepth (k + l) (A.val * B.val - B.val * A.val) at hd
  exact hd

 theorem unitriangularLieDepth_mem_iff (k : ℕ) (A : UnitriangularLieAlgebra n R) :
    A ∈ unitriangularLieDepth n k R ↔ MatrixDepth k A.val := Iff.rfl

 theorem unitriangularLieDepth_zero : unitriangularLieDepth n 0 R = ⊤ := by
  apply top_unique
  intro A _
  exact A.property.antitone (by omega)

 theorem unitriangularLieDepth_one : unitriangularLieDepth n 1 R = ⊤ := by
  apply top_unique
  intro A _
  exact A.property

 theorem unitriangularLieDepth_antitone : Antitone (fun k => unitriangularLieDepth n k R) := by
  intro k l hkl A hA
  exact hA.antitone hkl

 theorem unitriangularLieDepth_terminal {k : ℕ} (hk : n ≤ k) :
    unitriangularLieDepth n k R = ⊥ := by
  apply bot_unique
  intro A hA
  apply (LieSubmodule.mem_bot A).mpr
  apply Subtype.ext
  exact hA.eq_zero hk

 def unitriangularLieSingle (i j : Fin n) (hij : i < j) (c : R) :
    UnitriangularLieAlgebra n R :=
  ⟨Matrix.single i j c, matrixDepth_single_strict i j hij c⟩

 theorem unitriangularLieSingle_depth (k : ℕ) (i j : Fin n) (hij : i < j)
    (hgap : i.val + k ≤ j.val) (c : R) :
    unitriangularLieSingle i j hij c ∈ unitriangularLieDepth n k R := by
  intro a b hab
  apply Matrix.single_apply_of_ne
  intro h
  rcases h with ⟨rfl, rfl⟩
  omega

 theorem unitriangularLieSingle_bracket (i j l : Fin n) (hij : i < j) (hjl : j < l) (a b : R) :
    ⁅unitriangularLieSingle i j hij a, unitriangularLieSingle j l hjl b⁆ =
      unitriangularLieSingle i l (hij.trans hjl) (a * b) := by
  apply Subtype.ext
  change Matrix.single i j a * Matrix.single j l b -
    Matrix.single j l b * Matrix.single i j a = Matrix.single i l (a * b)
  rw [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne _ _ _ _
    (ne_of_lt (hij.trans hjl)).symm, sub_zero]

end Hindman168
