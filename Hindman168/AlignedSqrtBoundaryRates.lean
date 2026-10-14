import Hindman168.MasterShortBinCutoffDiscard
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Product margins at the actual modulus-aligned square-root microcell
scale are small relative to the master interval length. -/

namespace Hindman168

open Filter
open scoped Topology

theorem nat_sqrt_margin_ratio_sq_le {K R H : ℕ} (hH : 0 < H) (hR : R ≤ Nat.sqrt H) :
    ((K : ℝ) * R / H) ^ 2 ≤ (K : ℝ) ^ 2 / H := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hr2 : (R : ℝ) ^ 2 ≤ H := by
    exact_mod_cast (Nat.pow_le_pow_left hR 2).trans (Nat.sqrt_le' H)
  calc
    _ = ((K : ℝ) ^ 2 / (H : ℝ) ^ 2) * (R : ℝ) ^ 2 := by ring
    _ ≤ ((K : ℝ) ^ 2 / (H : ℝ) ^ 2) * H :=
      mul_le_mul_of_nonneg_left hr2 (by positivity)
    _ = _ := by field_simp

theorem nat_sqrt_margin_ratio_tendsto {κ : Type*} {l : Filter κ} (K R H : κ → ℕ)
    (hH : ∀ᶠ k in l, 0 < H k) (hR : ∀ᶠ k in l, R k ≤ Nat.sqrt (H k))
    (hK : Tendsto (fun k => (K k : ℝ) ^ 2 / H k) l (𝓝 0)) :
    Tendsto (fun k => (K k : ℝ) * R k / H k) l (𝓝 0) := by
  have hs : Tendsto (fun k => ((K k : ℝ) * R k / H k) ^ 2) l (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun _ => sq_nonneg _))
      ((hH.and hR).mono (fun _ hk => nat_sqrt_margin_ratio_sq_le hk.1 hk.2)) hK
  have ht := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hs
  change Tendsto (fun k => Real.sqrt (((K k : ℝ) * R k / H k) ^ 2)) l (𝓝 (Real.sqrt 0)) at ht
  have habs (k : κ) : |(K k : ℝ) * R k / H k| = (K k : ℝ) * R k / H k :=
    abs_of_nonneg (by positivity)
  simpa only [Real.sqrt_sq_eq_abs, Real.sqrt_zero, habs] using ht

theorem master_alignedSqrt_product_margin_tendsto
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (pivot : ℕ → Fin N) (K M : ℕ → ℕ)
    (hK : ∀ᶠ w in atTop, K w ≤ F.auxiliary w (pivot w).val) :
    Tendsto (fun w => (K w : ℝ) * (M w * (Nat.sqrt (F.gap w (pivot w).val) / M w) : ℕ) /
      F.gap w (pivot w).val) atTop (𝓝 0) := by
  have hg := PowerDominates.finite_choice (fun i : Fin N => hF.gap_growth i.val) pivot
  have hk2 : Tendsto (fun w => (K w : ℝ) ^ 2 / F.gap w (pivot w).val) atTop (𝓝 0) := by
    apply powerDominates_ratio_of_polynomial_bound hg 2 1
    filter_upwards [hK] with w hk
    have hkR : (K w : ℝ) ≤ F.auxiliary w (pivot w).val := by exact_mod_cast hk
    have hp := Nat.cast_nonneg (α := ℝ) (F.pool w (pivot w).val).upper
    have hk0 := Nat.cast_nonneg (α := ℝ) (K w)
    simp only [abs_sq, one_mul]
    nlinarith
  exact nat_sqrt_margin_ratio_tendsto K _ _
    (Eventually.of_forall (fun w => hF.gap_positive w (pivot w).val))
    (Eventually.of_forall (fun w => Nat.mul_div_le (Nat.sqrt (F.gap w (pivot w).val)) (M w))) hk2

end Hindman168
