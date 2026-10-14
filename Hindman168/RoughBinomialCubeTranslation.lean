import Hindman168.RoughBinomialToMonomial

namespace Hindman168
open MvPolynomial
open scoped BigOperators Classical

theorem rough_binomial_cube_untranslate {κ : Type*} [Fintype κ]
    (p : MvPolynomial κ ℝ) (q : ℕ) (hp : p.totalDegree ≤ q)
    (b : κ → ℤ) (α : (κ → ℕ) → ℝ) (c Z C A : ℝ)
    (hZ : 1 ≤ Z) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hb : ∀ j, |(b j : ℝ)| ≤ C*Z)
    (hrep : roughMvAffineSubstitution (fun j => (b j : ℝ)) (fun _ => 1) p =
      MvPolynomial.C c+∑ J ∈ roughSpatialDegreeIndices κ q,
        MvPolynomial.C (α J)*roughMvBinomialPolynomial J)
    (hα : ∀ J ∈ roughSpatialDegreeIndices κ q,
      ‖(α J : UnitAddCircle)‖ ≤ A*Z⁻¹^(∑ j, J j))
    (I : κ → ℕ) (hI : 0 < ∑ j, I j) :
    ‖(((roughBinomialMultiplier κ q : ℝ)*coeff (Finsupp.equivFunOnFinite.symm I) p : ℝ) :
      UnitAddCircle)‖ ≤
      (((roughSpatialDegreeIndices κ q).card : ℝ)*(2 : ℝ)^q*(max 1 C)^q*
        (roughBinomialCoefficientBudget κ q*A))*Z⁻¹^(∑ j, I j) := by
  let M : ℝ := roughBinomialMultiplier κ q
  have hdeg : (MvPolynomial.C M*p).totalDegree ≤ q := by
    exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, zero_add] using hp)
  have hshift : roughMvAffineSubstitution (fun j => (b j : ℝ)) (fun _ => 1)
      (MvPolynomial.C M*p) = MvPolynomial.C M*
        roughMvAffineSubstitution (fun j => (b j : ℝ)) (fun _ => 1) p := by
    rw [map_mul]
    simp only [roughMvAffineSubstitution, eval₂Hom_C]
  have h := rough_box_character_untranslate (MvPolynomial.C M*p) q hdeg b Z C
    (roughBinomialCoefficientBudget κ q*A) (lt_of_lt_of_le zero_lt_one hZ) hC
    (mul_nonneg (le_of_lt (rough_binomial_coefficient_budget_positive κ q)) hA) hb
    (fun J hJ => by
      rw [hshift, coeff_C_mul]
      exact rough_binomial_to_monomial_mod_one
        (roughMvAffineSubstitution (fun j => (b j : ℝ)) (fun _ => 1) p) q
        ((roughMvAffineSubstitution_degree _ _ _).trans hp) α c Z A hZ hA hrep hα J hJ) I hI
  simpa only [coeff_C_mul] using h

end Hindman168
