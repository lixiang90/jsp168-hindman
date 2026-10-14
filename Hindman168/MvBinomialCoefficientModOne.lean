import Hindman168.MvPolynomialBinomialExpansion
import Hindman168.ScalarBinomialCoefficientModOne

namespace Hindman168
open scoped BigOperators Classical

def mvBinomialCoefficientBudget (κ : Type*) [Fintype κ] (D : ℕ) : ℕ :=
  (scalarBinomialCoefficientBudget D)^(Fintype.card κ)

theorem mv_binomial_coefficient_budget_positive (κ : Type*) [Fintype κ] (D : ℕ) :
    0 < mvBinomialCoefficientBudget κ D :=
  Nat.pow_pos (scalar_binomial_coefficient_budget_positive D)

theorem mv_binomial_coefficient_row_budget {κ : Type*} [Fintype κ]
    (D : ℕ) (I : κ → ℕ) (hI : I ∈ mvBinomialBox κ D) :
    (∑ J ∈ mvBinomialBox κ D, mvBinomialStirlingWeight I J) ≤ mvBinomialCoefficientBudget κ D := by
  have he : (∑ J ∈ mvBinomialBox κ D, mvBinomialStirlingWeight I J) =
      ∏ j, ∑ t ∈ Finset.range (D+1), (I j).factorial*Nat.stirlingSecond t (I j) :=
    (Finset.prod_univ_sum (fun _ : κ => Finset.range (D+1))
      (fun j t => (I j).factorial*Nat.stirlingSecond t (I j))).symm
  rw [he]
  calc
    _ ≤ ∏ _j : κ, scalarBinomialCoefficientBudget D := by
      apply Finset.prod_le_prod (fun j _ => Nat.zero_le _)
      intro j _
      exact scalar_binomial_coefficient_row_budget D (I j) ((mv_binomial_box_mem D I).mp hI j)
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, mvBinomialCoefficientBudget]

/-- Actual INTEGER tensor Stirling weights preserve the ORIGINAL N^-|I|
scale. The lower weight distinguishes nonconstant and all-coefficient inputs,
without borrowing any missing constant bound. -/
theorem mv_binomial_coefficient_mod_one {κ : Type*} [Fintype κ]
    (p : MvPolynomial κ ℝ) (D q low : ℕ) (I : κ → ℕ) (hI : I ∈ mvBinomialBox κ D)
    (hlow : low ≤ ∑ j, I j) (N A : ℝ) (hN : 1 ≤ N) (hA : 0 ≤ A)
    (hcoeff : ∀ J ∈ mvBinomialBox κ D, low ≤ (∑ j, J j) →
      N^(∑ j, J j)*‖(((q : ℝ)*MvPolynomial.coeff
        (Finsupp.equivFunOnFinite.symm J) p : ℝ) : UnitAddCircle)‖ ≤ A) :
    N^(∑ j, I j)*‖(((q : ℝ)*mvPolynomialBinomialCoefficient p D I : ℝ) : UnitAddCircle)‖ ≤
      (mvBinomialCoefficientBudget κ D : ℝ)*A := by
  let w := fun J : κ → ℕ => (mvBinomialStirlingWeight I J : ℤ)
  let v := fun J : κ → ℕ => (q : ℝ)*MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J) p
  have he : (q : ℝ)*mvPolynomialBinomialCoefficient p D I =
      ∑ J ∈ mvBinomialBox κ D, (w J : ℝ)*v J := by
    rw [mvPolynomialBinomialCoefficient, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro J _
    dsimp only [w, v]
    push_cast
    ring
  rw [he]
  have hnorm := integer_weighted_mod_one_norm_bound (mvBinomialBox κ D) w v
  refine (mul_le_mul_of_nonneg_left hnorm (pow_nonneg (by linarith only [hN] : 0 ≤ N) _)).trans ?_
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ J ∈ mvBinomialBox κ D, (mvBinomialStirlingWeight I J : ℝ)*A := by
      apply Finset.sum_le_sum
      intro J hJ
      by_cases hz : mvBinomialStirlingWeight I J=0
      · simp only [w, hz, Int.cast_zero, abs_zero, zero_mul, Nat.cast_zero, mul_zero]
        exact le_rfl
      · have hij := mv_binomial_stirling_weight_weight_le I J hz
        have hv := hcoeff J hJ (hlow.trans hij)
        have hpow := pow_le_pow_right₀ hN hij
        have hw : 0 ≤ (mvBinomialStirlingWeight I J : ℝ) := by positivity
        have habs : |(w J : ℝ)| = (mvBinomialStirlingWeight I J : ℝ) := by
          dsimp only [w]
          rw [Int.cast_natCast, abs_of_nonneg hw]
        rw [habs]
        calc
          _ = (mvBinomialStirlingWeight I J : ℝ)*(N^(∑ j, I j)*‖(v J : UnitAddCircle)‖) := by ring
          _ ≤ (mvBinomialStirlingWeight I J : ℝ)*(N^(∑ j, J j)*‖(v J : UnitAddCircle)‖) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)) hw
          _ ≤ _ := mul_le_mul_of_nonneg_left hv hw
    _ = ((∑ J ∈ mvBinomialBox κ D, mvBinomialStirlingWeight I J : ℕ) : ℝ)*A := by
      rw [← Finset.sum_mul, Nat.cast_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast mv_binomial_coefficient_row_budget D I hI) hA

end Hindman168
