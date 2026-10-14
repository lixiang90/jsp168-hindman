import Hindman168.RoughBinomialCubeTranslation

namespace Hindman168
open MvPolynomial
open scoped BigOperators Classical

theorem rough_cube_coefficient_scale (q e : ℕ) (he : e ≤ q)
    (lam Z N A : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hZ : 0 < Z)
    (hN : lam*Z ≤ N) (hA : 0 ≤ A) :
    A*N⁻¹^e ≤ (A*lam⁻¹^q)*Z⁻¹^e := by
  have hN0 : 0 < N := (mul_pos hlam hZ).trans_le hN
  have hinv : N⁻¹ ≤ (lam*Z)⁻¹ := (inv_le_inv₀ hN0 (mul_pos hlam hZ)).mpr hN
  have hlaminv : 1 ≤ lam⁻¹ := (one_le_inv₀ hlam).mpr hlam1
  calc
    _ ≤ A*((lam*Z)⁻¹)^e := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (le_of_lt (inv_pos.mpr hN0)) hinv e) hA
    _ = A*(lam⁻¹^e*Z⁻¹^e) := by rw [mul_inv, mul_pow]
    _ ≤ A*(lam⁻¹^q*Z⁻¹^e) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hlaminv he) (by positivity)) hA
    _ = _ := by ring

theorem rough_binomial_cube_scale_untranslate {κ : Type*} [Fintype κ]
    (p : MvPolynomial κ ℝ) (q : ℕ) (hp : p.totalDegree ≤ q)
    (b : κ → ℤ) (α : (κ → ℕ) → ℝ) (c lam Z N C A : ℝ)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hZ : 1 ≤ Z)
    (hN : lam*Z ≤ N) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hb : ∀ j, |(b j : ℝ)| ≤ C*Z)
    (hrep : roughMvAffineSubstitution (fun j => (b j : ℝ)) (fun _ => 1) p =
      MvPolynomial.C c+∑ J ∈ roughSpatialDegreeIndices κ q,
        MvPolynomial.C (α J)*roughMvBinomialPolynomial J)
    (hα : ∀ J ∈ roughSpatialDegreeIndices κ q,
      ‖(α J : UnitAddCircle)‖ ≤ A*N⁻¹^(∑ j, J j))
    (I : κ → ℕ) (hI : 0 < ∑ j, I j) :
    ‖(((roughBinomialMultiplier κ q : ℝ)*coeff (Finsupp.equivFunOnFinite.symm I) p : ℝ) :
      UnitAddCircle)‖ ≤
      (((roughSpatialDegreeIndices κ q).card : ℝ)*(2 : ℝ)^q*(max 1 C)^q*
        (roughBinomialCoefficientBudget κ q*(A*lam⁻¹^q)))*Z⁻¹^(∑ j, I j) := by
  apply rough_binomial_cube_untranslate p q hp b α c Z C (A*lam⁻¹^q)
    hZ hC (by positivity) hb hrep _ I hI
  intro J hJ
  exact (hα J hJ).trans (rough_cube_coefficient_scale q (∑ j, J j)
    ((rough_spatial_degree_indices_mem q J).mp hJ).2 lam Z N A hlam hlam1
    (lt_of_lt_of_le zero_lt_one hZ) hN hA)

end Hindman168
