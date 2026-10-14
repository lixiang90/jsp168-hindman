import Hindman168.RoughNativeBoxBinomialTransfer
import Hindman168.RoughRealBoxCeil

namespace Hindman168
open MvPolynomial
open scoped BigOperators Classical

theorem rough_native_real_box_binomial_transfer {κ E ι : Type*} [Fintype κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : ι → E →ₗ[ℝ] ℝ) (s : Finset ι) (q : ℕ) (c C B η A : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hB : 0 ≤ B) (hη : 0 < η) (hA : 0 ≤ A) :
    ∃ A' Z0 : ℝ, 0 < A' ∧ 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ lo hi : κ → ℝ, (∀ j, c*Z ≤ hi j-lo j) →
      (∀ j, -C*Z ≤ lo j) → (∀ j, hi j ≤ C*Z) →
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
      η ≤ ‖finiteComplexSetMean (roughRealIntegerBox lo hi) f-mean‖ →
      ∃ i ∈ s, ∀ I : κ → ℕ, 0 < (∑ j, I j) →
        ‖((coeff (Finsupp.equivFunOnFinite.symm I)
          (roughScalarSpatialProjection ((roughBinomialMultiplier κ q : ℝ) • χ i) p z) : ℝ) :
          UnitAddCircle)‖ ≤ A'*Z⁻¹^(∑ j, I j) := by
  obtain ⟨A', Z0, hA', hZ0, hbox⟩ := rough_native_box_binomial_transfer (κ := κ) χ s q (c/2) (C+1)
    B η A (by positivity) (by linarith) hB hη hA
  refine ⟨A', max Z0 (2/c), hA', hZ0.trans (le_max_left _ _), ?_⟩
  intro Z hZ lo hi hlen hlo hhi p z hp f mean hf hinput hbad
  have hZbase : Z0 ≤ Z := (le_max_left _ _).trans hZ
  have hZ1 : 1 ≤ Z := hZ0.trans hZbase
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ1
  have hlarge : 2 ≤ c*Z := by
    have h := (div_le_iff₀ hc).mp ((le_max_right _ _).trans hZ)
    nlinarith
  have horder : ∀ j, lo j ≤ hi j := fun j => by
    have hp' := mul_pos hc hZpos
    linarith [hlen j]
  have he := rough_real_integer_box_width_representation lo hi horder
  have hbounds := rough_real_integer_box_scaled_bounds lo hi c C Z hc hZ1 hlarge hlen hlo hhi
  rw [he] at hbad
  exact hbox Z hZbase (fun j => ⌈lo j⌉) (roughRealBoxWidths lo hi)
    hbounds.1 hbounds.2.1 hbounds.2.2 p z hp f mean hf hinput hbad

end Hindman168
