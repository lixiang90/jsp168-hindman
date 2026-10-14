import Hindman168.ScalarPolynomialBinomialExpansion
import Hindman168.IntegerWeightedModOneNorm

namespace Hindman168
open Polynomial
open scoped BigOperators Classical

def scalarBinomialCoefficientBudget (D : ℕ) : ℕ :=
  1+∑ i ∈ Finset.range (D+1), ∑ j ∈ Finset.range (D+1),
    i.factorial*Nat.stirlingSecond j i

theorem scalar_binomial_coefficient_budget_positive (D : ℕ) :
    0 < scalarBinomialCoefficientBudget D := by
  dsimp only [scalarBinomialCoefficientBudget]
  omega

theorem scalar_binomial_coefficient_row_budget (D i : ℕ) (hi : i ≤ D) :
    (∑ j ∈ Finset.range (D+1), i.factorial*Nat.stirlingSecond j i) ≤
      scalarBinomialCoefficientBudget D := by
  have h : (∑ j ∈ Finset.range (D+1), i.factorial*Nat.stirlingSecond j i) ≤
      ∑ k ∈ Finset.range (D+1), ∑ j ∈ Finset.range (D+1),
        k.factorial*Nat.stirlingSecond j k := Finset.single_le_sum
    (f := fun i => ∑ j ∈ Finset.range (D+1), i.factorial*Nat.stirlingSecond j i)
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  dsimp only [scalarBinomialCoefficientBudget]
  omega

/-- Triangular INTEGER weights preserve the original N^-i error scale.
The lower index permits both the nonconstant inverse and the all-coefficient
small-value inverse, without importing any bound on the missing constant. -/
theorem scalar_binomial_coefficient_mod_one (p : ℝ[X]) (D q i low : ℕ)
    (hi : i ≤ D) (hlow : low ≤ i) (N A : ℝ) (hN : 1 ≤ N) (hA : 0 ≤ A)
    (hcoeff : ∀ j : ℕ, low ≤ j → j ≤ D →
      N^j*‖(((q : ℝ)*p.coeff j : ℝ) : UnitAddCircle)‖ ≤ A) :
    N^i*‖(((q : ℝ)*scalarPolynomialBinomialCoefficient p D i : ℝ) : UnitAddCircle)‖ ≤
      (scalarBinomialCoefficientBudget D : ℝ)*A := by
  let w := fun j => ((i.factorial*Nat.stirlingSecond j i : ℕ) : ℤ)
  let v := fun j => (q : ℝ)*p.coeff j
  have he : (q : ℝ)*scalarPolynomialBinomialCoefficient p D i =
      ∑ j ∈ Finset.range (D+1), (w j : ℝ)*v j := by
    dsimp only [scalarPolynomialBinomialCoefficient]
    rw [← mul_assoc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [w, v]
    push_cast
    ring
  rw [he]
  have hnorm := integer_weighted_mod_one_norm_bound (Finset.range (D+1)) w v
  refine (mul_le_mul_of_nonneg_left hnorm (pow_nonneg (by linarith : 0 ≤ N) i)).trans ?_
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ j ∈ Finset.range (D+1), ((i.factorial*Nat.stirlingSecond j i : ℕ) : ℝ)*A := by
      apply Finset.sum_le_sum
      intro j hj
      have hjD := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      by_cases hji : j < i
      · simp [w, Nat.stirlingSecond_eq_zero_of_lt hji]
      · have hij : i ≤ j := Nat.le_of_not_gt hji
        have hv := hcoeff j (hlow.trans hij) hjD
        have hpow := pow_le_pow_right₀ hN hij
        have hw : 0 ≤ ((i.factorial*Nat.stirlingSecond j i : ℕ) : ℝ) := by positivity
        have habs : |(w j : ℝ)| = ((i.factorial*Nat.stirlingSecond j i : ℕ) : ℝ) := by
          dsimp only [w]
          rw [Int.cast_natCast, abs_of_nonneg hw]
        rw [habs]
        calc
          _ = ((i.factorial*Nat.stirlingSecond j i : ℕ) : ℝ)*
              (N^i*‖(v j : UnitAddCircle)‖) := by ring
          _ ≤ ((i.factorial*Nat.stirlingSecond j i : ℕ) : ℝ)*
              (N^j*‖(v j : UnitAddCircle)‖) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)) hw
          _ ≤ _ := mul_le_mul_of_nonneg_left hv hw
    _ = ((∑ j ∈ Finset.range (D+1), i.factorial*Nat.stirlingSecond j i : ℕ) : ℝ)*A := by
      rw [← Finset.sum_mul, Nat.cast_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast scalar_binomial_coefficient_row_budget D i hi) hA

end Hindman168
