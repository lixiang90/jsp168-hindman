import Hindman168.RoughRealBoxCeil

namespace Hindman168
open scoped BigOperators Classical

theorem rough_corrected_real_box_cube_selection (κ : Type*) [Fintype κ]
    (c C B η : ℝ) (hc : 0 < c) (hB : 0 ≤ B) (hη : 0 < η) :
    ∃ lam : ℝ, 0 < lam ∧ lam ≤ 1 ∧
      ∃ Z0 : ℝ, 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
        ∀ lo hi : κ → ℝ, (∀ j, c*Z ≤ hi j-lo j) →
        (∀ j, -C*Z ≤ lo j) → (∀ j, hi j ≤ C*Z) →
        ∀ (f : (κ → ℤ) → ℂ) (mean : ℂ), (∀ x, ‖f x‖ ≤ B) →
        η ≤ ‖finiteComplexSetMean (roughRealIntegerBox lo hi) f-mean‖ →
        ∃ (N : ℕ) (b : κ → ℤ), 0 < N ∧
          (lam/2)*Z ≤ (N : ℝ) ∧ (N : ℝ) ≤ lam*Z ∧
          (∀ j, |(b j : ℝ)| ≤ (C+1)*Z) ∧
          (∀ v ∈ Fintype.piFinset (fun _ : κ => Finset.range N),
            (fun j => b j+(v j : ℤ)) ∈ roughRealIntegerBox lo hi) ∧
          η/2 ≤ ‖finiteComplexSetMean (Fintype.piFinset (fun _ : κ => Finset.range N))
            (fun v => f (fun j => b j+(v j : ℤ)))-mean‖ := by
  obtain ⟨lam, hlam, hlam1, Z0, hZ0, hcube⟩ :=
    rough_corrected_box_cube_selection κ (c/2) (C+1) B η (by positivity) hB hη
  refine ⟨lam, hlam, hlam1, max Z0 (2/c), hZ0.trans (le_max_left _ _), ?_⟩
  intro Z hZ lo hi hlen hlo hhi f mean hf hbad
  have hZbase : Z0 ≤ Z := (le_max_left _ _).trans hZ
  have hZ1 : 1 ≤ Z := hZ0.trans hZbase
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ1
  have hlarge : 2 ≤ c*Z := by
    have h := (div_le_iff₀ hc).mp ((le_max_right _ _).trans hZ)
    nlinarith
  have horder : ∀ j, lo j ≤ hi j := fun j => by
    have hp := mul_pos hc hZpos
    linarith [hlen j]
  have he := rough_real_integer_box_width_representation lo hi horder
  have hbounds := rough_real_integer_box_scaled_bounds lo hi c C Z hc hZ1 hlarge hlen hlo hhi
  rw [he] at hbad
  obtain ⟨N, b, hN, hNlo, hNhi, hb, hinside, hgap⟩ := hcube Z hZbase
    (fun j => ⌈lo j⌉) (roughRealBoxWidths lo hi) hbounds.1 hbounds.2.1 hbounds.2.2 f mean hf hbad
  refine ⟨N, b, hN, hNlo, hNhi, hb, ?_, hgap⟩
  intro v hv
  rw [he]
  exact hinside v hv

end Hindman168
