import Hindman168.RoughRationalExactness
import Mathlib.Algebra.Group.ForwardDiff

namespace Hindman168
open Polynomial
open scoped fwdDiff

theorem rough_fwdDiff_bound (f : ℕ → ℝ) (n z : ℕ) (A : ℝ)
    (h : ∀ j, j ≤ n → |f (z + j)| ≤ A) :
    |(Δ_[1]^[n] f) z| ≤ 2 ^ n * A := by
  induction n generalizing z with
  | zero => simpa using h 0 le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', fwdDiff]
    have h1 : |(Δ_[1]^[n] f) (z + 1)| ≤ 2 ^ n * A := by
      apply ih
      intro j hj
      have hh := h (j + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hh
    have h0 := ih z (fun j hj => h j (by omega))
    calc
      _ ≤ |(Δ_[1]^[n] f) (z + 1)| + |(Δ_[1]^[n] f) z| := abs_sub _ _
      _ ≤ 2 ^ n * A + 2 ^ n * A := add_le_add h1 h0
      _ = _ := by rw [pow_succ]; ring

theorem rough_fwdDiff_const (a : ℝ) (n : ℕ) (hn : 0 < n) :
    Δ_[(1 : ℕ)]^[n] (fun _ : ℕ => a) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [Function.iterate_succ_apply, fwdDiff_const]
  ext z
  simp [fwdDiff_iter_eq_sum_shift]

theorem rough_fwdDiff_intCast (f : ℕ → ℤ) (n z : ℕ) :
    (((Δ_[1]^[n] f) z : ℤ) : ℝ) = (Δ_[1]^[n] (fun j => (f j : ℝ))) z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', fwdDiff, Int.cast_sub, ih]

theorem rough_fwdDiff_polynomial_nat {R : Type*} [CommRing R]
    (P : R[X]) (n z : ℕ) :
    (Δ_[1]^[n] (fun j : ℕ => P.eval (j : R))) z = (Δ_[(1 : R)]^[n] P.eval) (z : R) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', fwdDiff, ih, Nat.cast_add, Nat.cast_one]

theorem rough_fwdDiff_polynomial_zero {R : Type*} [CommRing R]
    (P : R[X]) (q z : ℕ) (hP : P.natDegree ≤ q) :
    (Δ_[1]^[q + 1] (fun j : ℕ => P.eval (j : R))) z = 0 := by
  rw [rough_fwdDiff_polynomial_nat, Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (by omega : P.natDegree < q + 1)]
  rfl

end Hindman168
