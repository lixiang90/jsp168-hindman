import Hindman168.RoughNativeCharacterMultiplier

namespace Hindman168
open MvPolynomial
open scoped BigOperators Classical

theorem rough_scalar_spatial_projection_degree {κ E : Type*} [Fintype κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (χ : E →ₗ[ℝ] ℝ)
    (p : RoughVectorMvPolynomial (Option κ) E) (q : ℕ)
    (hp : RoughVectorMvDegreeLE p q) (z : ℝ) :
    (roughScalarSpatialProjection χ p z).totalDegree ≤ q := by
  unfold roughScalarSpatialProjection
  rw [totalDegree]
  apply Finset.sup_le
  intro I hI
  have hm := support_map_subset (Polynomial.evalRingHom z)
    (optionEquivRight ℝ κ (roughVectorMvProjection χ p)) hI
  have hs := rough_option_right_support_fixed (roughVectorMvProjection χ p) q
    (roughVectorMvProjection_degree χ hp) hm
  obtain hzero | hpos := Finset.mem_insert.mp hs
  · subst I
    simp
  · exact ((rough_spatial_degree_support_mem q I).mp hpos).2

theorem rough_native_binomial_cube_obstruction {κ E : Type*} [Fintype κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (χ : E →ₗ[ℝ] ℝ)
    (p : RoughVectorMvPolynomial (Option κ) E) (q : ℕ)
    (hp : RoughVectorMvDegreeLE p q) (z : ℝ)
    (b : κ → ℤ) (α : (κ → ℕ) → ℝ) (c lam Z N C A : ℝ)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hZ : 1 ≤ Z)
    (hN : lam*Z ≤ N) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hb : ∀ j, |(b j : ℝ)| ≤ C*Z)
    (hrep : roughMvAffineSubstitution (fun j => (b j : ℝ)) (fun _ => 1)
      (roughScalarSpatialProjection χ p z) =
      MvPolynomial.C c+∑ J ∈ roughSpatialDegreeIndices κ q,
        MvPolynomial.C (α J)*roughMvBinomialPolynomial J)
    (hα : ∀ J ∈ roughSpatialDegreeIndices κ q,
      ‖(α J : UnitAddCircle)‖ ≤ A*N⁻¹^(∑ j, J j))
    (I : κ → ℕ) (hI : 0 < ∑ j, I j) :
    ‖((coeff (Finsupp.equivFunOnFinite.symm I)
      (roughScalarSpatialProjection ((roughBinomialMultiplier κ q : ℝ) • χ) p z) : ℝ) :
      UnitAddCircle)‖ ≤
      (((roughSpatialDegreeIndices κ q).card : ℝ)*(2 : ℝ)^q*(max 1 C)^q*
        (roughBinomialCoefficientBudget κ q*(A*lam⁻¹^q)))*Z⁻¹^(∑ j, I j) := by
  rw [rough_scalar_spatial_projection_smul, coeff_C_mul]
  exact rough_binomial_cube_scale_untranslate (roughScalarSpatialProjection χ p z) q
    (rough_scalar_spatial_projection_degree χ p q hp z) b α c lam Z N C A
    hlam hlam1 hZ hN hC hA hb hrep hα I hI

end Hindman168
