import Hindman168.UnitriangularDepth

/-! Support bounds for actual matrix products. Depth k means every entry
with column index less than row index plus k is zero. Multiplication adds
depths, including depth zero, over an arbitrary commutative coefficient ring. -/

namespace Hindman168
open Matrix

variable {n : ℕ} {R : Type*} [CommRing R]

 def MatrixDepth (k : ℕ) (A : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j, j.val < i.val + k → A i j = 0

 theorem matrixDepth_zero (k : ℕ) : MatrixDepth k (0 : Matrix (Fin n) (Fin n) R) := by
  intro i j _
  rfl

 theorem MatrixDepth.add {k : ℕ} {A B : Matrix (Fin n) (Fin n) R}
    (hA : MatrixDepth k A) (hB : MatrixDepth k B) : MatrixDepth k (A + B) := by
  intro i j hij
  simp only [Matrix.add_apply, hA i j hij, hB i j hij, zero_add]

 theorem MatrixDepth.neg {k : ℕ} {A : Matrix (Fin n) (Fin n) R}
    (hA : MatrixDepth k A) : MatrixDepth k (-A) := by
  intro i j hij
  simp only [Matrix.neg_apply, hA i j hij, neg_zero]

 theorem MatrixDepth.sub {k : ℕ} {A B : Matrix (Fin n) (Fin n) R}
    (hA : MatrixDepth k A) (hB : MatrixDepth k B) : MatrixDepth k (A - B) := by
  simpa only [sub_eq_add_neg] using hA.add hB.neg

 theorem MatrixDepth.mul {k l : ℕ} {A B : Matrix (Fin n) (Fin n) R}
    (hA : MatrixDepth k A) (hB : MatrixDepth l B) : MatrixDepth (k + l) (A * B) := by
  classical
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro r _
  by_cases hr : r.val < i.val + k
  · rw [hA i r hr, zero_mul]
  · rw [hB r j (by omega), mul_zero]

 theorem MatrixDepth.antitone {k l : ℕ} {A : Matrix (Fin n) (Fin n) R}
    (hA : MatrixDepth l A) (hkl : k ≤ l) : MatrixDepth k A := by
  intro i j hij
  exact hA i j (by omega)

 theorem matrixDepth_zero_iff_upper {A : Matrix (Fin n) (Fin n) R} :
    MatrixDepth 0 A ↔ A.BlockTriangular id := by
  constructor
  · intro h i j hij
    exact h i j hij
  · intro h i j hij
    exact h hij

 def unitriangularDelta (u : Unitriangular n R) : Matrix (Fin n) (Fin n) R :=
  (u.val : Matrix (Fin n) (Fin n) R) - 1

 theorem unitriangular_matrixDepth_zero (u : Unitriangular n R) :
    MatrixDepth 0 (u.val : Matrix (Fin n) (Fin n) R) :=
  matrixDepth_zero_iff_upper.mpr u.property.1

 theorem unitriangularDepth_iff_delta (k : ℕ) (u : Unitriangular n R) :
    UnitriangularDepth k u ↔ MatrixDepth k (unitriangularDelta u) := by
  constructor
  · intro hu i j hij
    change (u.val : Matrix (Fin n) (Fin n) R) i j - (1 : Matrix (Fin n) (Fin n) R) i j = 0
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · rw [hu i j hlt hij, Matrix.one_apply_ne (ne_of_lt hlt), sub_self]
    · rw [u.property.2, Matrix.one_apply_eq, sub_self]
    · rw [u.property.1 hgt, Matrix.one_apply_ne (ne_of_gt hgt), sub_self]
  · intro hu i j hlt hij
    have h := hu i j hij
    change (u.val : Matrix (Fin n) (Fin n) R) i j - (1 : Matrix (Fin n) (Fin n) R) i j = 0 at h
    simpa only [Matrix.one_apply_ne (ne_of_lt hlt), sub_zero] using h

end Hindman168
