import Hindman168.PowerUnitEulerBounds
import Hindman168.PowerUnitZetaBound

/-!
# One uniform domination constant for the actual raw harmonic draws

For every sufficiently large X and every finite prime product W<=X, the
original harmonic law on [X,X^2) is bounded pointwise by 4 exp(3) times
the actual power-unit law with exponent 1+1/log X. The constant is paid
once per raw draw, with no dependence on the number of tested primes.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical

theorem comparison_unit_power_le_exp_one {X W : ℕ} (hX : 2 ≤ X)
    (hW : W ≤ X) : (W : ℝ) ^ (comparisonExponent X - 1) ≤ Real.exp 1 := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hl : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have he : comparisonExponent X - 1 = (Real.log (X : ℝ))⁻¹ := by
    simp [comparisonExponent]
  rw [he]
  calc
    _ ≤ (X : ℝ) ^ (Real.log (X : ℝ))⁻¹ :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hW) (inv_nonneg.mpr hl.le)
    _ = Real.exp 1 := by rw [Real.rpow_def_of_pos hX0, mul_inv_cancel₀ hl.ne']

theorem powerUnitNormalizer_comparison_bound {X : ℕ} (hX : 2 ≤ X)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hW : (∏ p ∈ S, p) ≤ X)
    (hZ : powerUnitNormalizer (comparisonExponent X) 1 ≤ 2 * Real.log (X : ℝ)) :
    powerUnitNormalizer (comparisonExponent X) (∏ p ∈ S, p) ≤
      2 * Real.exp 1 * unitDensity (∏ p ∈ S, p) * Real.log (X : ℝ) := by
  have hWp : 0 < ∏ p ∈ S, p := Finset.prod_pos (fun p hp => (hS p hp).pos)
  have htheta := (unitDensity_pos hWp).le
  have hpower := comparison_unit_power_le_exp_one hX hW
  calc
    _ ≤ powerUnitNormalizer (comparisonExponent X) 1 * unitDensity (∏ p ∈ S, p) *
        ((∏ p ∈ S, p : ℕ) : ℝ) ^ (comparisonExponent X - 1) :=
      (powerUnitNormalizer_prime_product_bounds (comparisonExponent_gt_one hX) S hS).2
    _ ≤ (2 * Real.log (X : ℝ)) * unitDensity (∏ p ∈ S, p) * Real.exp 1 := by
      gcongr
    _ = _ := by ring

theorem harmonicNormalizer_half_log_lower {X W : ℕ} (hX : 2 ≤ X)
    (hW : 0 < W) (hWX : W ≤ X) (hlog : 2 ≤ Real.log (X : ℝ)) :
    unitDensity W * Real.log (X : ℝ) / 2 ≤ harmonicNormalizer X W := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hr : (W : ℝ) / X ≤ 1 := (div_le_one hX0).mpr (by exact_mod_cast hWX)
  have ht : Real.log (X : ℝ) / 2 ≤ Real.log (X : ℝ) - (W : ℝ) / X := by linarith
  have hb : unitDensity W * Real.log (X : ℝ) / 2 ≤
      unitDensity W * (Real.log (X : ℝ) - (W : ℝ) / X) := by
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left ht (unitDensity_pos hW).le
  exact hb.trans (harmonicNormalizer_lower hX hW)

theorem harmonic_window_inverse_power_bound {X W n : ℕ} (hX : 2 ≤ X)
    (hn : n ∈ harmonicWindow X W) :
    (n : ℝ)⁻¹ ≤ Real.exp 2 * (n : ℝ) ^ (-comparisonExponent X) := by
  have hnX := Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hl : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have he : comparisonExponent X - 1 = (Real.log (X : ℝ))⁻¹ := by simp [comparisonExponent]
  have hpow : (n : ℝ) ^ (comparisonExponent X - 1) ≤ Real.exp 2 := by
    rw [he]
    calc
      _ ≤ ((X : ℝ) ^ 2) ^ (Real.log (X : ℝ))⁻¹ :=
        Real.rpow_le_rpow hn0.le (by exact_mod_cast hnX.2.le) (inv_nonneg.mpr hl.le)
      _ = Real.exp 2 := by
        rw [Real.rpow_def_of_pos (pow_pos hX0 _), Real.log_pow]
        congr 1
        field_simp
        norm_num
  have hidentity : (n : ℝ)⁻¹ =
      (n : ℝ) ^ (comparisonExponent X - 1) * (n : ℝ) ^ (-comparisonExponent X) := by
    rw [← Real.rpow_add hn0]
    have he : comparisonExponent X - 1 + -comparisonExponent X = (-1 : ℝ) := by ring
    rw [he, Real.rpow_neg_one]
  rw [hidentity]
  exact mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hn0.le _)

theorem harmonicWeight_le_powerUnitProbability {X : ℕ} (hX : 2 ≤ X)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hW : (∏ p ∈ S, p) ≤ X)
    (hlog : 2 ≤ Real.log (X : ℝ))
    (hZ : powerUnitNormalizer (comparisonExponent X) 1 ≤ 2 * Real.log (X : ℝ))
    (n : ℕ) :
    harmonicWeight X (∏ p ∈ S, p) n ≤
      (4 * Real.exp 3) * powerUnitProbability (comparisonExponent X) (∏ p ∈ S, p) n := by
  have hWp : 0 < ∏ p ∈ S, p := Finset.prod_pos (fun p hp => (hS p hp).pos)
  have hL0 : 0 < unitDensity (∏ p ∈ S, p) * Real.log (X : ℝ) :=
    mul_pos (unitDensity_pos hWp) (by linarith)
  have hH := harmonicNormalizer_half_log_lower hX hWp hW hlog
  have hH0 : 0 < harmonicNormalizer X (∏ p ∈ S, p) :=
    lt_of_lt_of_le (by positivity : 0 < unitDensity (∏ p ∈ S, p) * Real.log (X : ℝ) / 2) hH
  have hs := comparisonExponent_gt_one hX
  have hP0 := powerUnitNormalizer_pos hs (∏ p ∈ S, p)
  have hP := powerUnitNormalizer_comparison_bound hX S hS hW hZ
  have hratio : powerUnitNormalizer (comparisonExponent X) (∏ p ∈ S, p) ≤
      (4 * Real.exp 1) * harmonicNormalizer X (∏ p ∈ S, p) := by
    have he := mul_le_mul_of_nonneg_left hH (by positivity : (0 : ℝ) ≤ 4 * Real.exp 1)
    nlinarith [hP]
  by_cases hn : n ∈ harmonicWindow X (∏ p ∈ S, p)
  · have hco := (Finset.mem_filter.mp hn).2
    rw [harmonicWeight, if_pos hn, powerUnitProbability, powerUnitWeight, if_pos hco]
    apply (div_le_iff₀ hH0).mpr
    have hinv : (n : ℝ)⁻¹ ≤ Real.exp 2 * (n : ℝ) ^ (-comparisonExponent X) :=
      harmonic_window_inverse_power_bound hX hn
    have hscale : (n : ℝ) ^ (-comparisonExponent X) ≤
        (4 * Real.exp 1) * ((n : ℝ) ^ (-comparisonExponent X) /
          powerUnitNormalizer (comparisonExponent X) (∏ p ∈ S, p)) *
            harmonicNormalizer X (∏ p ∈ S, p) := by
      have he : (4 * Real.exp 1) * ((n : ℝ) ^ (-comparisonExponent X) /
          powerUnitNormalizer (comparisonExponent X) (∏ p ∈ S, p)) *
            harmonicNormalizer X (∏ p ∈ S, p) =
          ((4 * Real.exp 1) * (n : ℝ) ^ (-comparisonExponent X) *
            harmonicNormalizer X (∏ p ∈ S, p)) /
              powerUnitNormalizer (comparisonExponent X) (∏ p ∈ S, p) := by ring
      rw [he]
      apply (le_div_iff₀ hP0).mpr
      nlinarith [mul_le_mul_of_nonneg_left hratio
        (Real.rpow_nonneg (Nat.cast_nonneg n) (-comparisonExponent X))]
    have he : Real.exp 2 * (4 * Real.exp 1) = 4 * Real.exp 3 := by
      rw [mul_comm (4 : ℝ), ← mul_assoc, ← Real.exp_add]
      norm_num
      ring
    calc
      _ ≤ Real.exp 2 * (n : ℝ) ^ (-comparisonExponent X) := hinv
      _ ≤ Real.exp 2 * ((4 * Real.exp 1) *
          ((n : ℝ) ^ (-comparisonExponent X) /
            powerUnitNormalizer (comparisonExponent X) (∏ p ∈ S, p)) *
              harmonicNormalizer X (∏ p ∈ S, p)) :=
        mul_le_mul_of_nonneg_left hscale (Real.exp_pos 2).le
      _ = _ := by rw [← he]; ring
  · rw [harmonicWeight, if_neg hn]
    exact mul_nonneg (by positivity) (powerUnitProbability_nonneg hs _ n)

theorem harmonicWeight_powerUnit_eventual_domination :
    ∀ᶠ X : ℕ in atTop, ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
      (∏ p ∈ S, p) ≤ X → ∀ n : ℕ,
        harmonicWeight X (∏ p ∈ S, p) n ≤
          (4 * Real.exp 3) * powerUnitProbability (comparisonExponent X) (∏ p ∈ S, p) n := by
  have hl : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2, hl.eventually (eventually_ge_atTop 2),
    powerUnitNormalizer_comparison_eventually_le] with X hX hlog hZ
  intro S hS hW n
  exact harmonicWeight_le_powerUnitProbability hX S hS hW hlog hZ n

theorem harmonicWeight_product_le_powerUnit_product {ι : Type*} (T : Finset ι)
    (X : ι → ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hX : ∀ i ∈ T, 2 ≤ X i) (hW : ∀ i ∈ T, (∏ p ∈ S, p) ≤ X i)
    (hlog : ∀ i ∈ T, 2 ≤ Real.log (X i : ℝ))
    (hZ : ∀ i ∈ T, powerUnitNormalizer (comparisonExponent (X i)) 1 ≤
      2 * Real.log (X i : ℝ)) (n : ι → ℕ) :
    (∏ i ∈ T, harmonicWeight (X i) (∏ p ∈ S, p) (n i)) ≤
      (4 * Real.exp 3) ^ T.card *
        ∏ i ∈ T, powerUnitProbability (comparisonExponent (X i)) (∏ p ∈ S, p) (n i) := by
  have hWp : 0 < ∏ p ∈ S, p := Finset.prod_pos (fun p hp => (hS p hp).pos)
  have hnonneg : ∀ i ∈ T, 0 ≤ harmonicWeight (X i) (∏ p ∈ S, p) (n i) := by
    intro i hi
    have hl : 0 < unitDensity (∏ p ∈ S, p) * Real.log (X i : ℝ) / 2 :=
      div_pos (mul_pos (unitDensity_pos hWp) (by linarith [hlog i hi])) (by norm_num)
    exact harmonicWeight_nonneg (lt_of_lt_of_le hl
      (harmonicNormalizer_half_log_lower (hX i hi) hWp (hW i hi) (hlog i hi))) (n i)
  calc
    _ ≤ ∏ i ∈ T, ((4 * Real.exp 3) *
        powerUnitProbability (comparisonExponent (X i)) (∏ p ∈ S, p) (n i)) :=
      Finset.prod_le_prod hnonneg (fun i hi =>
        harmonicWeight_le_powerUnitProbability (hX i hi) S hS (hW i hi) (hlog i hi) (hZ i hi) (n i))
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const]

end Hindman168
