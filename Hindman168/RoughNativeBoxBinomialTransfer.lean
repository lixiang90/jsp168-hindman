import Hindman168.RoughCorrectedBoxCubeSelection
import Hindman168.RoughNativeBinomialObstruction

namespace Hindman168
open MvPolynomial
open scoped BigOperators Classical

theorem rough_native_box_binomial_transfer {κ E ι : Type*} [Fintype κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : ι → E →ₗ[ℝ] ℝ) (s : Finset ι) (q : ℕ) (c C B η A : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hB : 0 ≤ B) (hη : 0 < η) (hA : 0 ≤ A) :
    ∃ A' Z0 : ℝ, 0 < A' ∧ 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ (a : κ → ℤ) (width : κ → ℕ),
      (∀ j, c*Z ≤ (width j : ℝ)) → (∀ j, -C*Z ≤ (a j : ℝ)) →
      (∀ j, (a j : ℝ)+(width j : ℝ) ≤ C*Z) →
      ∀ (p : RoughVectorMvPolynomial (Option κ) E) (z : ℝ), RoughVectorMvDegreeLE p q →
      ∀ (f : (κ → ℤ) → ℂ) (mean : ℂ), (∀ x, ‖f x‖ ≤ B) →
      (∀ (N : ℕ) (b : κ → ℤ), 0 < N →
        η/2 ≤ ‖finiteComplexSetMean (Fintype.piFinset (fun _ : κ => Finset.range N))
          (fun v => f (fun j => b j+(v j : ℤ)))-mean‖ →
        ∃ i ∈ s, ∃ (α : (κ → ℕ) → ℝ) (c0 : ℝ),
          roughMvAffineSubstitution (fun j => (b j : ℝ)) (fun _ => 1)
            (roughScalarSpatialProjection (χ i) p z) =
              MvPolynomial.C c0+∑ J ∈ roughSpatialDegreeIndices κ q,
                MvPolynomial.C (α J)*roughMvBinomialPolynomial J ∧
          ∀ J ∈ roughSpatialDegreeIndices κ q,
            ‖(α J : UnitAddCircle)‖ ≤ A*(N : ℝ)⁻¹^(∑ j, J j)) →
      η ≤ ‖finiteComplexSetMean (roughIntegerWidthBox a width) f-mean‖ →
      ∃ i ∈ s, ∀ I : κ → ℕ, 0 < (∑ j, I j) →
        ‖((coeff (Finsupp.equivFunOnFinite.symm I)
          (roughScalarSpatialProjection ((roughBinomialMultiplier κ q : ℝ) • χ i) p z) : ℝ) :
          UnitAddCircle)‖ ≤ A'*Z⁻¹^(∑ j, I j) := by
  obtain ⟨lam, hlam, hlam1, Z0, hZ0, hcube⟩ :=
    rough_corrected_box_cube_selection κ c C B η hc hB hη
  let budget := ((roughSpatialDegreeIndices κ q).card : ℝ)*(2 : ℝ)^q*(max 1 C)^q*
    (roughBinomialCoefficientBudget κ q*(A*(lam/2)⁻¹^q))
  refine ⟨max 1 budget, Z0, lt_of_lt_of_le zero_lt_one (le_max_left _ _), hZ0, ?_⟩
  intro Z hZ a width hwidth hlo hhi p z hp f mean hf hinput hbad
  obtain ⟨N, b, hN, hNlo, _, hb, _, hgap⟩ := hcube Z hZ a width hwidth hlo hhi f mean hf hbad
  obtain ⟨i, hi, α, c0, hrep, hα⟩ := hinput N b hN hgap
  have hZpos : 0 < Z := zero_lt_one.trans_le (hZ0.trans hZ)
  refine ⟨i, hi, ?_⟩
  intro I hI
  have h := rough_native_binomial_cube_obstruction (χ i) p q hp z b α c0 (lam/2) Z N C A
    (by positivity) (by linarith) (hZ0.trans hZ) hNlo hC hA hb hrep hα I hI
  apply h.trans
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

end Hindman168
