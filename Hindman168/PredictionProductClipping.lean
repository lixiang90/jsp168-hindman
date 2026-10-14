import Hindman168.FiniteWeightedMomentProducts

/-!
# Fixed mixed products retain vanishing weighted clipping error

A finite product is expanded one factor at a time. A clipped factor has
its fixed absolute cap; each other product has a derived bounded second
moment. Weighted Cauchy--Schwarz then proves the full L1 error tends to
zero, including the empty product.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

theorem predictionClip_abs_le {K t : ℝ} (hK : 0 ≤ K) : |predictionClip K t| ≤ K := by
  apply abs_le.mpr
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

theorem prediction_product_clipping_error_tendsto {α ι : Type*}
    (μ : ℕ → Mass α) (H : ℕ → α → ℝ) (f : ι → ℕ → α → ℝ) (cut : ι → ℝ)
    (hμ : ∀ᶠ w in atTop, ∀ x, 0 ≤ μ w x)
    (hH : ∀ᶠ w in atTop, ∀ x, 0 ≤ H w x)
    (hbase : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ w in atTop, expectation (μ w) (H w) ≤ C)
    (hf : ∀ q, WeightedMomentBounded μ H (f q)) (hcut : ∀ q, 0 ≤ cut q)
    (hclip : ∀ q, Tendsto (fun w => expectation (μ w)
      (fun x => H w x * |f q w x - predictionClip (cut q) (f q w x)| ^ 2)) atTop (𝓝 0))
    (U : Finset ι) :
    Tendsto (fun w => expectation (μ w) (fun x => H w x *
      |(∏ q ∈ U, f q w x) - ∏ q ∈ U, predictionClip (cut q) (f q w x)|)) atTop (𝓝 0) := by
  induction U using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, sub_self, abs_zero, mul_zero]
    have he (w : ℕ) : expectation (μ w) (fun _ => 0) = 0 := by
      simp only [expectation, Finsupp.sum, mul_zero, Finset.sum_const_zero]
    simp only [he]
    exact tendsto_const_nhds
  | @insert q U hq ih =>
    let P w x := ∏ r ∈ U, f r w x
    let Q w x := ∏ r ∈ U, predictionClip (cut r) (f r w x)
    have hprod := weighted_moment_finset_prod μ H f hμ hH hbase hf U
    obtain ⟨B, hB, hb⟩ := hprod 2
    have he := weighted_l2_product_tendsto μ H
      (fun w x => f q w x - predictionClip (cut q) (f q w x)) P hμ hH (hclip q) B hB hb
    have ht : Tendsto (fun w => expectation (μ w)
        (fun x => H w x * |(f q w x - predictionClip (cut q) (f q w x)) * P w x|) +
        cut q * expectation (μ w) (fun x => H w x * |P w x - Q w x|)) atTop (𝓝 0) := by
      simpa only [mul_zero, add_zero] using he.add (ih.const_mul (cut q))
    apply squeeze_zero' ?_ ?_ ht
    · filter_upwards [hμ, hH] with w hw hHw
      exact expectation_nonneg _ _ hw (fun x => mul_nonneg (hHw x) (abs_nonneg _))
    · filter_upwards [hμ, hH] with w hw hHw
      simp only [Finset.prod_insert hq]
      have hp (x : α) : |f q w x * P w x - predictionClip (cut q) (f q w x) * Q w x| ≤
          |(f q w x - predictionClip (cut q) (f q w x)) * P w x| + cut q * |P w x - Q w x| := by
        have hid : f q w x * P w x - predictionClip (cut q) (f q w x) * Q w x =
            (f q w x - predictionClip (cut q) (f q w x)) * P w x +
              predictionClip (cut q) (f q w x) * (P w x - Q w x) := by ring
        rw [hid]
        have hm : |predictionClip (cut q) (f q w x) * (P w x - Q w x)| ≤
            cut q * |P w x - Q w x| := by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (predictionClip_abs_le (hcut q)) (abs_nonneg _)
        exact (abs_add_le _ _).trans (add_le_add le_rfl hm)
      calc
        _ ≤ expectation (μ w) (fun x => H w x *
            (|(f q w x - predictionClip (cut q) (f q w x)) * P w x| +
              cut q * |P w x - Q w x|)) :=
          expectation_mono _ _ _ hw (fun x => mul_le_mul_of_nonneg_left (hp x) (hHw x))
        _ = _ := by
          simp only [mul_add, expectation_add]
          rw [← expectation_const_mul]
          congr 1
          apply congrArg (expectation (μ w))
          funext x
          ring

end Hindman168
