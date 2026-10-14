import Hindman168.PositivePrincipalSumPivotTranslation
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Hindman168
open Filter
open scoped Topology

/-- Actual displacement/cutoff growth makes the original harmonic L1 bound
vanish. These are scale hypotheses, not an assumed small probability error. -/
theorem principal_harmonic_boundary_tendsto {K : Type*} (L : Filter K)
    (X W H : K → ℝ)
    (hX : Tendsto X L atTop)
    (hWX : Tendsto (fun w => W w / X w) L (𝓝 0))
    (hHX : Tendsto (fun w => H w / X w) L (𝓝 0))
    (hH : ∀ᶠ w in L, 0 ≤ H w) :
    Tendsto (fun w => 2 * H w / (X w * (Real.log (X w) - W w / X w))) L (𝓝 0) := by
  have hx : ∀ᶠ w in L, 0 < X w := hX.eventually (eventually_gt_atTop 0)
  have hl : ∀ᶠ w in L, 2 ≤ Real.log (X w) :=
    (Real.tendsto_log_atTop.comp hX).eventually (eventually_ge_atTop 2)
  have hw : ∀ᶠ w in L, W w / X w < 1 := hWX.eventually (gt_mem_nhds (by norm_num))
  have hupper : Tendsto (fun w => 2 * (H w / X w)) L (𝓝 0) := by
    simpa using hHX.const_mul 2
  apply squeeze_zero' _ _ hupper
  · filter_upwards [hx, hl, hw, hH] with w hx hl hw hh
    exact div_nonneg (mul_nonneg (by norm_num) hh)
      (mul_nonneg hx.le (by linarith))
  · filter_upwards [hx, hl, hw, hH] with w hx hl hw hh
    rw [div_mul_eq_div_div]
    have hn : 0 ≤ 2 * H w / X w := div_nonneg (mul_nonneg (by norm_num) hh) hx.le
    have hb := div_le_self hn (show 1 ≤ Real.log (X w) - W w / X w by linarith)
    calc
      _ ≤ 2 * H w / X w := hb
      _ = _ := by ring
end Hindman168
