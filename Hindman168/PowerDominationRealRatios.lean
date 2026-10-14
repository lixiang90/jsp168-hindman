import Hindman168.PowerGrowth
import Mathlib.Order.Filter.AtTopBot.Basic

/-! Recover every positive REAL-exponent paper ratio from genuine domination
of natural powers. Positivity is explicit, including the denominator. -/
namespace Hindman168
open Filter
open scoped Topology

theorem rough_power_domination_real_ratios {α : Type*} {l : Filter α} {S Z : α → ℝ}
    (hg : PowerDominates l Z S) (hS : ∀ᶠ w in l, 1 ≤ S w)
    (hZ : ∀ᶠ w in l, 0 ≤ Z w) :
    ∀ a : ℝ, 0 < a → Tendsto (fun w => Z w/(S w)^a) l atTop := by
  intro a _ha
  apply tendsto_atTop.2
  intro b
  let A := max b 1
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_right b 1)
  filter_upwards [hg.eventually_bound hZ (hS.mono (fun _ hs => zero_le_one.trans hs))
    ⌈a⌉₊ hA,hS] with w hw hs
  have hspos : 0 < S w := zero_lt_one.trans_le hs
  have hpow : (S w)^a ≤ (S w)^⌈a⌉₊ := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hs (Nat.le_ceil a)
  have hden : 0 < (S w)^a := Real.rpow_pos_of_pos hspos a
  apply (le_div_iff₀ hden).mpr
  calc
    b*(S w)^a ≤ A*(S w)^a := mul_le_mul_of_nonneg_right (le_max_left b 1) hden.le
    _ ≤ A*(S w)^⌈a⌉₊ := mul_le_mul_of_nonneg_left hpow hA.le
    _ ≤ Z w := hw

end Hindman168
