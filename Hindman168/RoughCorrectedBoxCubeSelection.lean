import Hindman168.RoughEqualCubeRatioChoice

namespace Hindman168
open scoped BigOperators Classical

theorem rough_corrected_box_cube_selection (κ : Type*) [Fintype κ]
    (c C B η : ℝ) (hc : 0 < c) (hB : 0 ≤ B) (hη : 0 < η) :
    ∃ lam : ℝ, 0 < lam ∧ lam ≤ 1 ∧
      ∃ Z0 : ℝ, 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
        ∀ (a : κ → ℤ) (width : κ → ℕ),
        (∀ j, c*Z ≤ (width j : ℝ)) →
        (∀ j, -C*Z ≤ (a j : ℝ)) →
        (∀ j, (a j : ℝ)+(width j : ℝ) ≤ C*Z) →
        ∀ (f : (κ → ℤ) → ℂ) (mean : ℂ), (∀ x, ‖f x‖ ≤ B) →
        η ≤ ‖finiteComplexSetMean (roughIntegerWidthBox a width) f-mean‖ →
        ∃ (N : ℕ) (b : κ → ℤ), 0 < N ∧
          (lam/2)*Z ≤ (N : ℝ) ∧ (N : ℝ) ≤ lam*Z ∧
          (∀ j, |(b j : ℝ)| ≤ C*Z) ∧
          (∀ v ∈ Fintype.piFinset (fun _ : κ => Finset.range N),
            (fun j => b j+(v j : ℤ)) ∈ roughIntegerWidthBox a width) ∧
          η/2 ≤ ‖finiteComplexSetMean (Fintype.piFinset (fun _ : κ => Finset.range N))
            (fun v => f (fun j => b j+(v j : ℤ)))-mean‖ := by
  obtain ⟨lam, hlam, hlam1, hlamc, hratio⟩ := rough_equal_cube_small_ratio κ c B η hc hB hη
  refine ⟨lam, hlam, hlam1, max 1 (2/lam), le_max_left _ _, ?_⟩
  intro Z hZ a width hwidth hlo hhi f mean hf hbad
  have hZ1 : 1 ≤ Z := (le_max_left _ _).trans hZ
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ1
  have hZlarge : 2/lam ≤ Z := (le_max_right _ _).trans hZ
  have hlarge : 2 ≤ lam*Z := by
    have h := (div_le_iff₀ hlam).mp hZlarge
    nlinarith
  let N := ⌊lam*Z⌋₊
  obtain ⟨hN, hNlo, hNhi⟩ := rough_equal_cube_side_floor lam Z hlam hZ0 hlarge
  have hNwidth := rough_equal_cube_side_floor_fits width c lam Z hlam hZ0 hlamc hwidth
  have hfrac := rough_equal_box_boundary_fraction_scaled a width N hN c Z lam hc hZ0 hwidth hNhi
  have hmul := mul_le_mul_of_nonneg_left hfrac (show 0 ≤ 2*B by positivity)
  have hboundary : 2*B*((roughIntegerWidthBox a width \ roughEqualTiledBox a width N).card : ℝ)/
      (roughIntegerWidthBox a width).card ≤ η/4 := by
    have hr : 2*B*((Fintype.card κ : ℝ)*lam/c) ≤ η/4 := by
      simpa only [mul_div_assoc, mul_assoc] using hratio
    simpa only [mul_div_assoc] using hmul.trans hr
  obtain ⟨r, hgap⟩ := rough_equal_cube_haar_selection a width N hN hNwidth f mean B η
    (η/4) hB hf hboundary hbad
  refine ⟨N, roughEqualCubeOrigin a N (fun j => (r j).val), hN, ?_, hNhi,
    rough_equal_cube_origin_bound a width N hN r C Z hlo hhi, ?_, ?_⟩
  · nlinarith
  · intro v hv
    apply rough_equal_cube_contained a width N r
    rw [← rough_equal_cube_sample_image]
    exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
  · linarith

end Hindman168
