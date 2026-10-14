import Hindman168.FiniteRetainedProbabilityError

namespace Hindman168
open Filter
open scoped BigOperators Topology

theorem MasterParameterConditions.aligned_interior_normalized_test_tendsto
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (gap pivot : ℕ → Fin N)
    (horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val)
    (f : ℕ → ℤ → ℝ) (hf : ∀ w y, |f w y| ≤ 1) :
    Tendsto (fun w =>
      let X := F.cutoff w (pivot w).val
      let R := F.gap w (gap w).val
      let S := Finset.Ico (((X : ℤ) / R + 1) * R) (((X ^ 2 : ℕ) : ℤ) / R * R)
      |(∑ y ∈ Finset.Ico (X : ℤ) (X ^ 2 : ℕ), integerMass X (primorial w) y * f w y) -
        (∑ y ∈ S, integerMass X (primorial w) y * f w y) /
          (∑ y ∈ S, integerMass X (primorial w) y)|) atTop (𝓝 0) := by
  have he := (hF.aligned_endpoint_loss_tendsto gap pivot horder).const_mul 2
  simp only [mul_zero] at he
  apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _ he
  filter_upwards [hF.nil_boundary_raw_geometry pivot,
    hF.aligned_interior_mass_eventually_positive gap pivot horder] with w hw hp
  let X := F.cutoff w (pivot w).val
  let R := F.gap w (gap w).val
  have hz : 0 < harmonicNormalizer X (primorial w) :=
    (harmonicNormalizer_boundary_lower hw.1 (primorial_pos w) hw.2.1 hw.2.2).1
  apply finite_retained_probability_test_error _ _ _ _ (f w)
    (integerMass_nonnegative X (primorial w)) (hf w) _ hp
  · intro y hy
    obtain ⟨hl, hu⟩ := Finset.mem_Ico.mp hy
    have hb := alignedInterior_endpoint_bounds (X : ℤ) (X ^ 2 : ℕ) R (hF.gap_positive w (gap w).val)
    exact Finset.mem_Ico.mpr ⟨hb.1.trans hl, hu.trans_le hb.2.2.2⟩
  · rw [integerMass_window_sum, integerMass_total hz]

end Hindman168
