import Hindman168.PredictionDualMomentDomination
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Clipping transfers from every fixed natural moment

The moment order is chosen after the desired error and remains fixed as
w tends to infinity. A strict threshold K>A makes the later geometric
limit vanish. Positive p is required, since the zeroth error power is one.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def predictionClip (K t : ℝ) : ℝ := max (-K) (min K t)

theorem predictionClip_eq_self {K t : ℝ} (ht : |t| ≤ K) : predictionClip K t = t := by
  obtain ⟨hl, hu⟩ := abs_le.mp ht
  simp only [predictionClip, min_eq_right hu, max_eq_right hl]

theorem predictionClip_error_le_abs {K t : ℝ} (hK : 0 ≤ K) :
    |t - predictionClip K t| ≤ |t| := by
  by_cases hu : t ≤ K
  · by_cases hl : -K ≤ t
    · simp only [predictionClip, min_eq_right hu, max_eq_right hl, sub_self, abs_zero]
      exact abs_nonneg _
    · have hn : t < -K := lt_of_not_ge hl
      have hs : t - -K ≤ 0 := by linarith
      simp only [predictionClip, min_eq_right hu, max_eq_left hn.le, abs_of_nonpos hs]
      linarith [neg_le_abs t]
  · have ht : K < t := lt_of_not_ge hu
    have hm : -K ≤ K := by linarith
    have hs : 0 ≤ t - K := by linarith
    simp only [predictionClip, min_eq_left ht.le, max_eq_right hm, abs_of_nonneg hs]
    linarith [le_abs_self t]

theorem predictionClip_error_power_bound {K t : ℝ} (hK : 0 < K) (p k : ℕ) (hp : 0 < p) :
    |t - predictionClip K t| ^ p ≤ |t| ^ (p + k) / K ^ k := by
  by_cases ht : |t| ≤ K
  · rw [predictionClip_eq_self ht, sub_self, abs_zero, zero_pow (by omega : p ≠ 0)]
    exact div_nonneg (pow_nonneg (abs_nonneg _) _) (pow_nonneg hK.le _)
  · have hu : K ≤ |t| := (lt_of_not_ge ht).le
    apply (le_div_iff₀ (pow_pos hK k)).mpr
    calc
      _ ≤ |t| ^ p * K ^ k := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (abs_nonneg _)
          (predictionClip_error_le_abs hK.le) p) (pow_nonneg hK.le _)
      _ ≤ |t| ^ p * |t| ^ k := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hK.le hu k) (pow_nonneg (abs_nonneg _) _)
      _ = _ := (pow_add _ _ _).symm

theorem prediction_clip_weighted_power_bound {α : Type*} (μ : Mass α)
    (hμ : ∀ x, 0 ≤ μ x) (H f : α → ℝ) (hH : ∀ x, 0 ≤ H x)
    {K : ℝ} (hK : 0 < K) (p k : ℕ) (hp : 0 < p) :
    expectation μ (fun x => H x * |f x - predictionClip K (f x)| ^ p) ≤
      expectation μ (fun x => H x * |f x| ^ (p + k)) / K ^ k := by
  calc
    _ ≤ expectation μ (fun x => H x * (|f x| ^ (p + k) / K ^ k)) :=
      expectation_mono _ _ _ hμ (fun x => mul_le_mul_of_nonneg_left
        (predictionClip_error_power_bound hK p k hp) (hH x))
    _ = _ := by
      simp only [expectation, Finsupp.sum, div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul]

theorem prediction_clip_error_tendsto_of_moments {α : Type*}
    (μ : ℕ → Mass α) (H f : ℕ → α → ℝ)
    (hμ : ∀ᶠ w in atTop, ∀ x, 0 ≤ μ w x)
    (hH : ∀ᶠ w in atTop, ∀ x, 0 ≤ H w x)
    (A C K : ℝ) (hA : 0 ≤ A) (hK : 0 < K) (hAK : A < K)
    (hMom : ∀ b : ℕ, ∀ᶠ w in atTop,
      expectation (μ w) (fun x => H w x * |f w x| ^ b) ≤ C * A ^ b)
    (p : ℕ) (hp : 0 < p) :
    Tendsto (fun w => expectation (μ w)
      (fun x => H w x * |f w x - predictionClip K (f w x)| ^ p)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [hμ, hH] with w hw hHw
    exact lt_of_lt_of_le ha (expectation_nonneg _ _ hw
      (fun x => mul_nonneg (hHw x) (pow_nonneg (abs_nonneg _) _)))
  · intro ε hε
    have hr : 0 ≤ A / K := div_nonneg hA hK.le
    have hr1 : A / K < 1 := (div_lt_one hK).mpr hAK
    have hg := (tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).const_mul (C * A ^ p)
    have hg0 : Tendsto (fun k : ℕ => C * A ^ p * (A / K) ^ k) atTop (𝓝 0) := by
      simpa only [mul_zero] using hg
    obtain ⟨k, hk⟩ := (hg0.eventually (Iio_mem_nhds hε)).exists
    filter_upwards [hμ, hH, hMom (p + k)] with w hw hHw hm
    have hclip := prediction_clip_weighted_power_bound (μ w) hw (H w) (f w) hHw hK p k hp
    have hb : expectation (μ w) (fun x => H w x * |f w x - predictionClip K (f w x)| ^ p) ≤
        C * A ^ p * (A / K) ^ k := by
      calc
        _ ≤ expectation (μ w) (fun x => H w x * |f w x| ^ (p + k)) / K ^ k := hclip
        _ ≤ (C * A ^ (p + k)) / K ^ k := div_le_div_of_nonneg_right hm (pow_nonneg hK.le _)
        _ = _ := by rw [pow_add, div_pow]; ring
    exact hb.trans_lt hk

end Hindman168
