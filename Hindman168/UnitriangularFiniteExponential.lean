import Hindman168.UnitriangularMatrixSeries
import Mathlib.RingTheory.Nilpotent.Exp

/-! A uniform finite exponential polynomial on matrices. On every strictly
upper-triangular matrix it equals the genuine nilpotent exponential. The
nonlinear difference improves support by at least one superdiagonal. -/

namespace Hindman168
open Matrix

variable {n : ℕ} {R : Type*} [CommRing R] [Algebra ℚ R]

 noncomputable def matrixFiniteExp (A : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  ∑ r ∈ Finset.range (n + 2), (r.factorial : ℚ)⁻¹ • A ^ r

 theorem matrixFiniteExp_eq_exp {A : Matrix (Fin n) (Fin n) R} (hA : MatrixDepth 1 A) :
    matrixFiniteExp A = IsNilpotent.exp A := by
  apply (IsNilpotent.exp_eq_sum ?_).symm
  have hp : MatrixDepth (n + 2) (A ^ (n + 2)) := by
    simpa only [Nat.one_mul] using hA.pow (n + 2)
  exact hp.eq_zero (by omega)

 theorem matrixFiniteExp_expansion (A : Matrix (Fin n) (Fin n) R) :
    matrixFiniteExp A = 1 + A +
      ∑ r ∈ Finset.range n, ((r + 2).factorial : ℚ)⁻¹ • A ^ (r + 2) := by
  unfold matrixFiniteExp
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [Nat.zero_add, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one,
    inv_one, one_smul, pow_zero, pow_one]
  abel

 theorem matrixFiniteExp_zero : matrixFiniteExp (0 : Matrix (Fin n) (Fin n) R) = 1 := by
  rw [matrixFiniteExp_expansion]
  simp

 theorem matrixFiniteExp_unitriangular {A : Matrix (Fin n) (Fin n) R} (hA : MatrixDepth 1 A) :
    IsUnitriangular (matrixFiniteExp A) := by
  apply (matrixDepth_sub_one_iff_unitriangular _).mp
  rw [matrixFiniteExp_expansion]
  have hs : MatrixDepth 1 (∑ r ∈ Finset.range n,
      ((r + 2).factorial : ℚ)⁻¹ • A ^ (r + 2)) := by
    apply MatrixDepth.sum
    intro r _
    have hp : MatrixDepth (r + 2) (A ^ (r + 2)) := by
      simpa only [Nat.one_mul] using hA.pow (r + 2)
    exact (hp.antitone (by omega)).smul _
  have heq : 1 + A + (∑ r ∈ Finset.range n,
      ((r + 2).factorial : ℚ)⁻¹ • A ^ (r + 2)) - 1 = A +
      (∑ r ∈ Finset.range n, ((r + 2).factorial : ℚ)⁻¹ • A ^ (r + 2)) := by abel
  rw [heq]
  exact hA.add hs

 theorem matrixFiniteExp_difference_depth {k : ℕ} {A B : Matrix (Fin n) (Fin n) R}
    (hA : MatrixDepth 1 A) (hB : MatrixDepth 1 B) (hd : MatrixDepth k (A - B)) :
    MatrixDepth (k + 1) (matrixFiniteExp A - matrixFiniteExp B - (A - B)) := by
  rw [matrixFiniteExp_expansion, matrixFiniteExp_expansion]
  have heq : (1 + A + ∑ r ∈ Finset.range n, ((r + 2).factorial : ℚ)⁻¹ • A ^ (r + 2)) -
      (1 + B + ∑ r ∈ Finset.range n, ((r + 2).factorial : ℚ)⁻¹ • B ^ (r + 2)) - (A - B) =
      ∑ r ∈ Finset.range n, ((r + 2).factorial : ℚ)⁻¹ • (A ^ (r + 2) - B ^ (r + 2)) := by
    simp only [smul_sub, Finset.sum_sub_distrib]
    abel
  rw [heq]
  apply MatrixDepth.sum
  intro r _
  have hp := matrixDepth_power_difference hA hB hd (r + 2) (by omega)
  exact (hp.antitone (by omega)).smul _

 theorem matrixFiniteExp_injective {A B : Matrix (Fin n) (Fin n) R}
    (hA : MatrixDepth 1 A) (hB : MatrixDepth 1 B) (heq : matrixFiniteExp A = matrixFiniteExp B) : A = B := by
  have hd : ∀ k, MatrixDepth (k + 1) (A - B) := by
    intro k
    induction k with
    | zero => exact hA.sub hB
    | succ k ih =>
      have h := matrixFiniteExp_difference_depth hA hB ih
      rw [heq, sub_self, zero_sub] at h
      simpa only [neg_neg] using h.neg
  exact sub_eq_zero.mp ((hd n).eq_zero (by omega))

end Hindman168
