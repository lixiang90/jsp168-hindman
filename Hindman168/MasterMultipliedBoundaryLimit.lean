import Hindman168.AveragedMultipliedBoundary
import Hindman168.AlignedSqrtBoundaryRates

/-! The averaged product-boundary discard vanishes at the actual master
scales and modulus-aligned square-root widths. Support assumptions describe
the original outside tail products and all required numerical margins. -/

namespace Hindman168

open FiniteMass Filter
open scoped Topology Classical

theorem master_multipliedBoundary_alignedSqrt_tendsto
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (pivot : ℕ → Fin N) (K M : ℕ → ℕ) (J : ℕ)
    {α : Type*} (μ : ℕ → Mass α) (t B : ℕ → α → ℕ)
    (hK : ∀ᶠ w in atTop, K w ≤ F.auxiliary w (pivot w).val)
    (hout : ∀ᶠ w in atTop, (∀ x, 0 ≤ μ w x) ∧ total (μ w) = 1 ∧
      ∀ x ∈ (μ w).support, 0 < t w x ∧ (primorial w).Coprime (t w x) ∧ t w x ≤ K w ∧
        B w x ≤ J * K w * (M w * (Nat.sqrt (F.gap w (pivot w).val) / M w))) :
    Tendsto (fun w => event
      (conditionalJoint (μ w) (fun _ => rawMass (F.cutoff w (pivot w).val) (primorial w)))
      (fun xp => ¬ intervalInteriorRoot (F.gap w (pivot w).val) (B w xp.1)
        ((t w xp.1 * xp.2 : ℕ) : ℤ))) atTop (𝓝 0) := by
  apply joint_multipliedBoundary_tendsto μ t B
    (fun w => F.cutoff w (pivot w).val) primorial (fun w => F.gap w (pivot w).val) K
    (fun w => J * K w * (M w * (Nat.sqrt (F.gap w (pivot w).val) / M w)))
  · filter_upwards [hout, hF.nil_boundary_raw_geometry pivot] with w hw hg
    exact ⟨hw.1, hw.2.1, hg.1, primorial_pos w, hF.gap_positive w (pivot w).val,
      hg.2.1, hg.2.2, hw.2.2⟩
  · have hm := (master_alignedSqrt_product_margin_tendsto hF pivot K M hK).const_mul (J : ℝ)
    simpa only [Nat.cast_mul, mul_assoc, mul_div_assoc, mul_zero] using hm
  · exact hF.nil_boundary_period_ratio_tendsto pivot K hK
  · have he := hF.nil_boundary_endpoint_ratio_tendsto pivot pivot (fun _ => 1)
      (Eventually.of_forall (fun _ => le_rfl))
      (Eventually.of_forall (fun w => (Nat.le_add_left 1 1).trans
        (F.auxiliary_ge_two w (pivot w).val)))
    simpa only [Nat.mul_one] using he

end Hindman168
