import Hindman168.PowerUnitEulerFactors
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The zeta pole bound for the actual comparison normalizer

Mathlib's proved real zeta residue theorem gives a common eventual bound
Z(1+1/log X) <= 2 log X, independent of the prime exclusions.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology

noncomputable def comparisonExponent (X : ℕ) : ℝ := 1 + (Real.log (X : ℝ))⁻¹

theorem comparisonExponent_gt_one {X : ℕ} (hX : 2 ≤ X) :
    1 < comparisonExponent X := by
  have hXr : (1 : ℝ) < X := by exact_mod_cast (by omega : 1 < X)
  exact lt_add_of_pos_right _ (inv_pos.mpr (Real.log_pos hXr))

theorem powerUnitNormalizer_one_eq_zeta {s : ℝ} (hs : 1 < s) :
    (powerUnitNormalizer s 1 : ℂ) = riemannZeta (s : ℂ) := by
  rw [powerUnitNormalizer_one, Complex.ofReal_tsum,
    zeta_eq_tsum_one_div_nat_cpow (by simpa using hs)]
  apply tsum_congr
  intro n
  simp only [Real.rpow_neg (Nat.cast_nonneg n), Complex.ofReal_inv, one_div,
    Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]

theorem powerUnitNormalizer_prime_product_eq_zeta_re {s : ℝ} (hs : 1 < s)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    powerUnitNormalizer s (∏ p ∈ S, p) =
      (riemannZeta (s : ℂ)).re * ∏ p ∈ S, (1 - (p : ℝ) ^ (-s)) := by
  have he := congrArg Complex.re (powerUnitNormalizer_one_eq_zeta hs)
  simp only [Complex.ofReal_re] at he
  rw [powerUnitNormalizer_prime_product hs S hS, ← powerUnitNormalizer_one, he]

theorem powerUnitNormalizer_one_pole :
    Tendsto (fun s : ℝ => (s - 1) * powerUnitNormalizer s 1)
      (𝓝[>] 1) (𝓝 1) := by
  simpa only [powerUnitNormalizer_one, Real.rpow_neg (Nat.cast_nonneg _), one_div]
    using tendsto_sub_mul_tsum_nat_rpow

theorem comparisonExponent_tendsto :
    Tendsto comparisonExponent atTop (𝓝[>] (1 : ℝ)) := by
  have hl : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hi := tendsto_inv_atTop_zero.comp hl
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, ?_⟩
  · change Tendsto (fun X : ℕ => 1 + (Real.log (X : ℝ))⁻¹) atTop (𝓝 1)
    simpa only [Function.comp_apply, add_zero] using tendsto_const_nhds.add hi
  · filter_upwards [eventually_ge_atTop 2] with X hX
    exact comparisonExponent_gt_one hX

theorem powerUnitNormalizer_comparison_eventually_le :
    ∀ᶠ X : ℕ in atTop,
      powerUnitNormalizer (comparisonExponent X) 1 ≤ 2 * Real.log (X : ℝ) := by
  have ht := powerUnitNormalizer_one_pole.comp comparisonExponent_tendsto
  filter_upwards [eventually_ge_atTop 2,
    ht.eventually (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2))] with X hX h
  have hl : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have he : comparisonExponent X - 1 = (Real.log (X : ℝ))⁻¹ := by
    simp [comparisonExponent]
  change (comparisonExponent X - 1) * powerUnitNormalizer (comparisonExponent X) 1 < 2 at h
  rw [he, mul_comm, ← div_eq_mul_inv, div_lt_iff₀ hl] at h
  exact h.le

end Hindman168
