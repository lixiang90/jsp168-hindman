import Hindman168.ScalarPolynomialRecoveryWeights
import Hindman168.IntegerWeightedModOneNorm

namespace Hindman168
open Polynomial
open scoped BigOperators Classical

theorem scalar_polynomial_one_based_small_values_card (p : ℝ[X]) (N : ℕ) (ε : ℝ) :
    ((Finset.range N).filter (fun n : ℕ =>
      ‖((p.eval ((n+1 : ℕ) : ℝ) : ℝ) : UnitAddCircle)‖ ≤ ε)).card =
    ((Finset.Icc 1 N).filter (fun n : ℕ =>
      ‖((p.eval (n : ℝ) : ℝ) : UnitAddCircle)‖ ≤ ε)).card := by
  apply Finset.card_bij (fun n _ => n+1)
  · intro n hn
    have hv := Finset.mem_filter.mp hn
    have hnr := Finset.mem_range.mp hv.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hv.2⟩
  · intro n _ m _ hnm
    omega
  · intro n hn
    have hv := Finset.mem_filter.mp hn
    have hb := Finset.mem_Icc.mp hv.1
    have he : n-1+1=n := by omega
    refine ⟨n-1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩, he⟩
    simpa only [he] using hv.2

/-- Recover every ORIGINAL coefficient from the actual shift p(X+1).
The constant changes under translation and is recovered with the same
integer triangular sum as the other coefficients. -/
theorem scalar_polynomial_unit_shift_recovery (p : ℝ[X]) (D q i : ℕ)
    (hp : p.natDegree ≤ D) (N A : ℝ) (hN : 1 ≤ N) (hA : 0 ≤ A)
    (hcoeff : ∀ j : ℕ, j ≤ D →
      N^j*‖(((q : ℝ)*(scalarPolynomialOnProgression p 1 1).coeff j : ℝ) :
        UnitAddCircle)‖ ≤ A) :
    N^i*‖(((q : ℝ)*p.coeff i : ℝ) : UnitAddCircle)‖ ≤
      (D+1 : ℕ)*(2 : ℝ)^D*A := by
  let w := scalarProgressionRecoveryWeight 1 1 D i
  let v := fun j => (q : ℝ)*(scalarPolynomialOnProgression p 1 1).coeff j
  have he : (q : ℝ)*p.coeff i = ∑ j ∈ Finset.range (D+1), (w j : ℝ)*v j := by
    have h := scalar_polynomial_integer_coefficient_recovery p 1 1 D i hp
    simp only [Nat.cast_one, one_pow, one_mul] at h
    rw [h, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [w, v]
    ring
  rw [he]
  have hnorm := integer_weighted_mod_one_norm_bound (Finset.range (D+1)) w v
  refine (mul_le_mul_of_nonneg_left hnorm (pow_nonneg (by linarith : 0 ≤ N) i)).trans ?_
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ _j ∈ Finset.range (D+1), (2 : ℝ)^D*A := by
      apply Finset.sum_le_sum
      intro j hj
      have hjD := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      by_cases hji : j < i
      · dsimp only [w]
        rw [scalar_progression_recovery_weight_zero_below 1 1 D i j hji]
        simp only [Int.cast_zero, abs_zero, zero_mul, mul_zero]
        positivity
      · have hij : i ≤ j := Nat.le_of_not_gt hji
        have hw : |(w j : ℝ)| ≤ (2 : ℝ)^D := by
          simpa only [Nat.cast_one, one_pow, one_mul, mul_one] using
            scalar_progression_recovery_weight_bound 1 1 D i j 1 (by omega) le_rfl hjD
        have hv := hcoeff j hjD
        have hpow := pow_le_pow_right₀ hN hij
        calc
          _ = |(w j : ℝ)| * (N^i*‖(v j : UnitAddCircle)‖) := by ring
          _ ≤ |(w j : ℝ)| * (N^j*‖(v j : UnitAddCircle)‖) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)) (abs_nonneg _)
          _ ≤ (2 : ℝ)^D*A := mul_le_mul hw hv (by positivity) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end Hindman168
