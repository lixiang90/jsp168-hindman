import Hindman168.PrimeAPWindow
import Hindman168.WeightedAbel

/-!
# Actual natural prefix discrepancies from the verified AP-PNT input

The Abel transformation uses range(n), whereas the PNT input uses a
closed prefix. The successor identity below accounts for this endpoint
for every n, including prime endpoints. No endpoint term is discarded.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology

noncomputable def primeLogRange (q a n : ℕ) : ℝ :=
  ∑ p ∈ Finset.range n,
    if p.Prime then (if p % q = a then Real.log p else 0) else 0

theorem primeLogRange_succ (q a n : ℕ) :
    primeLogRange q a (n + 1) = primeLogPrefix q a (n : ℝ) := by
  have hI : Finset.range (n + 1) = Finset.Iic n := by
    ext p
    simp only [Finset.mem_range, Finset.mem_Iic]
    omega
  unfold primeLogRange primeLogPrefix
  rw [Nat.floor_natCast, Finset.sum_filter, hI]

theorem primeLogRange_div_tendsto {q a : ℕ} (hq : 1 ≤ q)
    (ha : a.Coprime q) (haq : a < q) :
    Tendsto (fun n : ℕ => primeLogRange q a n / n) atTop (𝓝 (1 / q.totient)) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  have ht := (primeLogPrefix_div_tendsto hq ha haq).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hm := ht.mul (tendsto_natCast_div_add_atTop (1 : ℝ))
  simp only [mul_one] at hm
  apply hm.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [primeLogRange_succ]
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  field_simp

theorem primeResidueLogCoefficient_range (q a n : ℕ) :
    (∑ p ∈ Finset.range n, primeResidueLogCoefficient q a p) =
      primeLogRange q a n - primeLogRange 1 0 n / q.totient := by
  unfold primeLogRange
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p.Prime <;> simp [primeResidueLogCoefficient, hp, Nat.mod_one]

theorem primeResidueLogCoefficient_prefix_div_tendsto {q a : ℕ} (hq : 1 ≤ q)
    (ha : a.Coprime q) (haq : a < q) :
    Tendsto (fun n : ℕ => (∑ p ∈ Finset.range n, primeResidueLogCoefficient q a p) / n)
      atTop (𝓝 0) := by
  have ht := (primeLogRange_div_tendsto hq ha haq).sub
    ((primeLogRange_div_tendsto (by decide : 1 ≤ 1)
      (by decide : Nat.Coprime 0 1) (by decide : 0 < 1)).div_const (q.totient : ℝ))
  simp only [Nat.totient_one, Nat.cast_one, div_one, sub_self] at ht
  apply ht.congr
  intro n
  rw [primeResidueLogCoefficient_range, sub_div, div_right_comm]

theorem primeResidueLogCoefficient_prefix_small {q a : ℕ} (hq : 1 ≤ q)
    (ha : a.Coprime q) (haq : a < q) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, |∑ p ∈ Finset.range n, primeResidueLogCoefficient q a p| ≤ ε * n := by
  have ht := (primeResidueLogCoefficient_prefix_div_tendsto hq ha haq).abs
  simp only [abs_zero] at ht
  filter_upwards [ht.eventually (eventually_lt_nhds hε), eventually_ge_atTop 1] with n hn hn1
  rw [abs_div, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] at hn
  have hp : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  exact ((div_lt_iff₀ hp).mp hn).le

theorem primeHarmonicResidue_dyadic_eventually_error {q a : ℕ} (hq : 1 ≤ q)
    (ha : a.Coprime q) (haq : a < q) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      |primeHarmonicResidue q a (2 ^ n) (2 ^ (n + 1)) -
        primePoolHarmonicMass (2 ^ n) (2 ^ (n + 1)) / q.totient| ≤
      4 * ε / Real.log (2 ^ n : ℕ) := by
  obtain ⟨L, hL⟩ := eventually_atTop.mp (primeResidueLogCoefficient_prefix_small hq ha haq hε)
  filter_upwards [dyadic_atTop.eventually (eventually_ge_atTop (max L 2))] with n hn
  have hA : 2 ≤ 2 ^ n := (le_max_right L 2).trans hn
  have hAL : L ≤ 2 ^ n := (le_max_left L 2).trans hn
  have hb := primeHarmonicResidue_dyadic_error a hq hA hε.le (fun k hk =>
    hL k (hAL.trans (Finset.mem_Icc.mp hk).1))
  simpa only [Nat.pow_succ, Nat.mul_comm] using hb

end Hindman168
