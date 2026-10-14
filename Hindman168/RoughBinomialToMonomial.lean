import Hindman168.RoughBinomialCoefficientBudget

namespace Hindman168
open MvPolynomial
open scoped BigOperators Classical

def roughBinomialMultiplier (κ : Type*) [Fintype κ] (q : ℕ) : ℕ :=
  q.factorial^(Fintype.card κ)

theorem rough_binomial_multiplier_positive (κ : Type*) [Fintype κ] (q : ℕ) :
    0 < roughBinomialMultiplier κ q := by
  exact Nat.pow_pos (Nat.factorial_pos q)

theorem rough_binomial_to_monomial_mod_one {κ : Type*} [Fintype κ]
    (p : MvPolynomial κ ℝ) (q : ℕ) (hp : p.totalDegree ≤ q)
    (α : (κ → ℕ) → ℝ) (c Z A : ℝ) (hZ : 1 ≤ Z) (hA : 0 ≤ A)
    (hrep : p = C c+∑ J ∈ roughSpatialDegreeIndices κ q,
      C (α J)*roughMvBinomialPolynomial J)
    (hα : ∀ J ∈ roughSpatialDegreeIndices κ q,
      ‖(α J : UnitAddCircle)‖ ≤ A*Z⁻¹^(∑ j, J j))
    (I : κ → ℕ) (hI : 0 < ∑ j, I j) :
    ‖(((roughBinomialMultiplier κ q : ℝ)*coeff (Finsupp.equivFunOnFinite.symm I) p : ℝ) :
      UnitAddCircle)‖ ≤ (roughBinomialCoefficientBudget κ q*A)*Z⁻¹^(∑ j, I j) := by
  by_cases hIq : (∑ j, I j) ≤ q
  · have hIs : I ∈ roughSpatialDegreeIndices κ q :=
      (rough_spatial_degree_indices_mem q I).mpr ⟨hI, hIq⟩
    have hJ : ∀ J ∈ roughSpatialDegreeIndices κ q, ∀ j, J j ≤ q := by
      intro J hJs j
      exact (Finset.single_le_sum (fun k _ => Nat.zero_le (J k)) (Finset.mem_univ j)).trans
        ((rough_spatial_degree_indices_mem q J).mp hJs).2
    have hc := rough_binomial_cleared_positive_coefficient q (roughSpatialDegreeIndices κ q)
      α c hJ I hI
    rw [← hrep] at hc
    simpa only [roughBinomialMultiplier, Nat.cast_pow, hc] using
      rough_binomial_coefficient_mod_one q α Z A hZ hA hα I hIs
  · have hz : coeff (Finsupp.equivFunOnFinite.symm I) p = 0 := by
      apply notMem_support_iff.mp
      intro hmem
      have hdeg := (le_totalDegree hmem).trans hp
      have hs : (Finsupp.equivFunOnFinite.symm I).sum (fun _ e => e) = ∑ j, I j := by
        rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Finsupp.coe_equivFunOnFinite_symm]
      rw [hs] at hdeg
      exact hIq hdeg
    rw [hz, mul_zero, AddCircle.coe_zero, norm_zero]
    exact mul_nonneg (mul_nonneg (le_of_lt (rough_binomial_coefficient_budget_positive κ q)) hA)
      (pow_nonneg (inv_nonneg.mpr (le_trans zero_le_one hZ)) _)

end Hindman168
