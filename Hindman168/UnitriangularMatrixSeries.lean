import Hindman168.UnitriangularMatrixDepth

/-! Finite matrix series and their support differences. Multiplication is
actual matrix multiplication. No exponential inverse or logarithm is assumed. -/

namespace Hindman168
open Matrix

variable {n : ℕ} {R : Type*} [CommRing R]

 theorem MatrixDepth.smul {S : Type*} [SMulZeroClass S R] {k : ℕ}
    {A : Matrix (Fin n) (Fin n) R} (hA : MatrixDepth k A) (s : S) : MatrixDepth k (s • A) := by
  intro i j hij
  change s • A i j = 0
  rw [hA i j hij, smul_zero]

 theorem MatrixDepth.sum {ι : Type*} {k : ℕ} (s : Finset ι)
    (f : ι → Matrix (Fin n) (Fin n) R) (hf : ∀ i ∈ s, MatrixDepth k (f i)) :
    MatrixDepth k (∑ i ∈ s, f i) := by
  intro a b hab
  simp only [Matrix.sum_apply]
  change (∑ i ∈ s, f i a b) = 0
  exact Finset.sum_eq_zero fun i hi => hf i hi a b hab

 theorem matrixDepth_one : MatrixDepth 0 (1 : Matrix (Fin n) (Fin n) R) := by
  intro i j hij
  exact Matrix.one_apply_ne (by intro h; subst j; omega)

 theorem MatrixDepth.pow {k : ℕ} {A : Matrix (Fin n) (Fin n) R}
    (hA : MatrixDepth k A) (m : ℕ) : MatrixDepth (k * m) (A ^ m) := by
  induction m with
  | zero => simpa only [Nat.mul_zero, pow_zero] using matrixDepth_one (n := n) (R := R)
  | succ m ih =>
    simpa only [pow_succ, Nat.mul_succ] using ih.mul hA

 theorem MatrixDepth.eq_zero {k : ℕ} {A : Matrix (Fin n) (Fin n) R}
    (hA : MatrixDepth k A) (hnk : n ≤ k) : A = 0 := by
  ext i j
  exact hA i j (by omega)

 theorem MatrixDepth.nilpotent {A : Matrix (Fin n) (Fin n) R}
    (hA : MatrixDepth 1 A) : IsNilpotent A := by
  refine ⟨n + 2, ?_⟩
  have hp : MatrixDepth (n + 2) (A ^ (n + 2)) := by
    simpa only [Nat.one_mul] using hA.pow (n + 2)
  exact hp.eq_zero (by omega)

 theorem matrixDepth_sub_one_iff_unitriangular (A : Matrix (Fin n) (Fin n) R) :
    MatrixDepth 1 (A - 1) ↔ IsUnitriangular A := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i j hij
      change j < i at hij
      have hz := h i j (by omega)
      change A i j - (1 : Matrix (Fin n) (Fin n) R) i j = 0 at hz
      simpa only [Matrix.one_apply_ne (ne_of_gt hij), sub_zero] using hz
    · intro i
      have hz := h i i (by omega)
      change A i i - (1 : Matrix (Fin n) (Fin n) R) i i = 0 at hz
      simpa only [Matrix.one_apply_eq, sub_eq_zero] using hz
  · intro h i j hij
    change A i j - (1 : Matrix (Fin n) (Fin n) R) i j = 0
    by_cases heq : i = j
    · subst j
      rw [h.2, Matrix.one_apply_eq, sub_self]
    · have hji : j < i := by omega
      rw [h.1 hji, Matrix.one_apply_ne (ne_of_gt hji), sub_self]

 theorem matrixDepth_unitriangular_difference {A B : Matrix (Fin n) (Fin n) R}
    (hA : IsUnitriangular A) (hB : IsUnitriangular B) : MatrixDepth 1 (A - B) := by
  have ha := (matrixDepth_sub_one_iff_unitriangular A).mpr hA
  have hb := (matrixDepth_sub_one_iff_unitriangular B).mpr hB
  have heq : (A - 1) - (B - 1) = A - B := by abel
  exact heq ▸ ha.sub hb

 theorem matrixDepth_power_difference {k : ℕ} {A B : Matrix (Fin n) (Fin n) R}
    (hA : MatrixDepth 1 A) (hB : MatrixDepth 1 B) (hd : MatrixDepth k (A - B))
    (r : ℕ) (hr : 1 ≤ r) : MatrixDepth (k + (r - 1)) (A ^ r - B ^ r) := by
  induction r with
  | zero => omega
  | succ r ih =>
    by_cases hz : r = 0
    · subst r
      simpa only [Nat.zero_add, pow_one, Nat.sub_self, Nat.add_zero] using hd
    · have hprev := ih (by omega)
      have hpow : MatrixDepth r (B ^ r) := by simpa only [Nat.one_mul] using hB.pow r
      have hleft := hprev.mul hA
      have hright := hpow.mul hd
      have heq : A ^ (r + 1) - B ^ (r + 1) =
          (A ^ r - B ^ r) * A + B ^ r * (A - B) := by
        rw [pow_succ, pow_succ]
        noncomm_ring
      rw [heq]
      have he : k + (r - 1) + 1 = k + r := by omega
      have he' : k + (r + 1 - 1) = k + r := by omega
      rw [he']
      exact (he ▸ hleft).add (by simpa only [Nat.add_comm r k] using hright)

end Hindman168
