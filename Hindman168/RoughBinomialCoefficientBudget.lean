import Hindman168.RoughBinomialClearedExpansion
import Hindman168.RoughModOneIntegerCombination

namespace Hindman168
open MvPolynomial
open scoped BigOperators Classical

noncomputable def roughBinomialCoefficientBudget (κ : Type*) [Fintype κ] (q : ℕ) : ℝ :=
  max 1 (∑ I ∈ roughSpatialDegreeIndices κ q, ∑ J ∈ roughSpatialDegreeIndices κ q,
    |((coeff (Finsupp.equivFunOnFinite.symm I) (roughMvClearedBinomialPolynomial q J) : ℤ) : ℝ)|)

theorem rough_binomial_coefficient_budget_positive (κ : Type*) [Fintype κ] (q : ℕ) :
    0 < roughBinomialCoefficientBudget κ q :=
  lt_of_lt_of_le (by norm_num) (le_max_left _ _)

theorem rough_binomial_coefficient_budget_row {κ : Type*} [Fintype κ]
    (q : ℕ) (I : κ → ℕ) (hI : I ∈ roughSpatialDegreeIndices κ q) :
    (∑ J ∈ roughSpatialDegreeIndices κ q,
      |((coeff (Finsupp.equivFunOnFinite.symm I) (roughMvClearedBinomialPolynomial q J) : ℤ) : ℝ)|) ≤
        roughBinomialCoefficientBudget κ q := by
  have hnonneg : ∀ K ∈ roughSpatialDegreeIndices κ q, 0 ≤
      ∑ J ∈ roughSpatialDegreeIndices κ q,
        |((coeff (Finsupp.equivFunOnFinite.symm K) (roughMvClearedBinomialPolynomial q J) : ℤ) : ℝ)| :=
    fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  exact (Finset.single_le_sum hnonneg hI).trans (le_max_right _ _)

theorem rough_binomial_coefficient_mod_one {κ : Type*} [Fintype κ]
    (q : ℕ) (α : (κ → ℕ) → ℝ) (Z A : ℝ) (hZ : 1 ≤ Z) (hA : 0 ≤ A)
    (hα : ∀ J ∈ roughSpatialDegreeIndices κ q,
      ‖(α J : UnitAddCircle)‖ ≤ A*Z⁻¹^(∑ j, J j))
    (I : κ → ℕ) (hI : I ∈ roughSpatialDegreeIndices κ q) :
    ‖((∑ J ∈ roughSpatialDegreeIndices κ q,
      ((coeff (Finsupp.equivFunOnFinite.symm I) (roughMvClearedBinomialPolynomial q J) : ℤ) : ℝ)*α J : ℝ) :
      UnitAddCircle)‖ ≤ (roughBinomialCoefficientBudget κ q*A)*Z⁻¹^(∑ j, I j) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hiZ : 0 ≤ Z⁻¹ := le_of_lt (inv_pos.mpr hZ0)
  have hiZ1 : Z⁻¹ ≤ 1 := (inv_le_one₀ hZ0).mpr hZ
  calc
    _ ≤ ∑ J ∈ roughSpatialDegreeIndices κ q,
        |((coeff (Finsupp.equivFunOnFinite.symm I) (roughMvClearedBinomialPolynomial q J) : ℤ) : ℝ)| *
          ‖(α J : UnitAddCircle)‖ := rough_mod_one_integer_combination _ _ _
    _ ≤ ∑ J ∈ roughSpatialDegreeIndices κ q,
        |((coeff (Finsupp.equivFunOnFinite.symm I) (roughMvClearedBinomialPolynomial q J) : ℤ) : ℝ)| *
          (A*Z⁻¹^(∑ j, I j)) := by
      apply Finset.sum_le_sum
      intro J hJ
      by_cases hIJ : ∀ j, I j ≤ J j
      · have hsum : (∑ j, I j) ≤ ∑ j, J j := Finset.sum_le_sum (fun j _ => hIJ j)
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact (hα J hJ).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one hiZ hiZ1 hsum) hA)
      · rw [rough_mv_cleared_binomial_coeff_zero q I J hIJ, Int.cast_zero, abs_zero,
          zero_mul, zero_mul]
    _ = (∑ J ∈ roughSpatialDegreeIndices κ q,
        |((coeff (Finsupp.equivFunOnFinite.symm I) (roughMvClearedBinomialPolynomial q J) : ℤ) : ℝ)|)*
          (A*Z⁻¹^(∑ j, I j)) := by rw [Finset.sum_mul]
    _ ≤ roughBinomialCoefficientBudget κ q*(A*Z⁻¹^(∑ j, I j)) :=
      mul_le_mul_of_nonneg_right (rough_binomial_coefficient_budget_row q I hI) (by positivity)
    _ = _ := by ring

end Hindman168
