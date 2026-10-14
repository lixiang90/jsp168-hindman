import Mathlib.Analysis.PSeries
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic

/-!
# Actual power-weighted laws on the W-units

These are laws on all natural numbers, with zero mass at zero, not finite
truncations. The normalizer is the actual sum of the positive W-unit weights.
The comparison with the zeta Euler factors is proved separately.
-/

namespace Hindman168

open scoped BigOperators Classical

noncomputable def powerUnitWeight (s : ℝ) (W n : ℕ) : ℝ :=
  if n.Coprime W then (n : ℝ) ^ (-s) else 0

noncomputable def powerUnitNormalizer (s : ℝ) (W : ℕ) : ℝ :=
  ∑' n : ℕ, powerUnitWeight s W n

noncomputable def powerUnitProbability (s : ℝ) (W n : ℕ) : ℝ :=
  powerUnitWeight s W n / powerUnitNormalizer s W

theorem powerUnitWeight_nonneg (s : ℝ) (W n : ℕ) :
    0 ≤ powerUnitWeight s W n := by
  unfold powerUnitWeight
  split_ifs
  · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · exact le_rfl

theorem powerUnitWeight_summable {s : ℝ} (hs : 1 < s) (W : ℕ) :
    Summable (powerUnitWeight s W) := by
  apply (Real.summable_nat_rpow.mpr (by linarith : -s < -1)).of_nonneg_of_le
    (powerUnitWeight_nonneg s W)
  intro n
  unfold powerUnitWeight
  split_ifs
  · exact le_rfl
  · exact Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem powerUnitWeight_zero {s : ℝ} (hs : 1 < s) (W : ℕ) :
    powerUnitWeight s W 0 = 0 := by
  simp [powerUnitWeight, Real.zero_rpow (by linarith : -s ≠ 0)]

theorem powerUnitWeight_one (s : ℝ) (W : ℕ) :
    powerUnitWeight s W 1 = 1 := by
  simp [powerUnitWeight]

theorem powerUnitNormalizer_ge_one {s : ℝ} (hs : 1 < s) (W : ℕ) :
    1 ≤ powerUnitNormalizer s W := by
  simpa only [powerUnitNormalizer, powerUnitWeight_one] using
    (Summable.le_tsum (powerUnitWeight_summable hs W) 1
      (fun n _ => powerUnitWeight_nonneg s W n))

theorem powerUnitNormalizer_pos {s : ℝ} (hs : 1 < s) (W : ℕ) :
    0 < powerUnitNormalizer s W :=
  lt_of_lt_of_le zero_lt_one (powerUnitNormalizer_ge_one hs W)

theorem powerUnitProbability_nonneg {s : ℝ} (hs : 1 < s) (W n : ℕ) :
    0 ≤ powerUnitProbability s W n :=
  div_nonneg (powerUnitWeight_nonneg s W n) (powerUnitNormalizer_pos hs W).le

theorem powerUnitProbability_summable {s : ℝ} (hs : 1 < s) (W : ℕ) :
    Summable (powerUnitProbability s W) :=
  (powerUnitWeight_summable hs W).div_const _

theorem powerUnitProbability_tsum {s : ℝ} (hs : 1 < s) (W : ℕ) :
    ∑' n : ℕ, powerUnitProbability s W n = 1 := by
  unfold powerUnitProbability
  rw [tsum_div_const]
  exact div_self (powerUnitNormalizer_pos hs W).ne'

noncomputable def powerUnitPMF (s : ℝ) (hs : 1 < s) (W : ℕ) : PMF ℕ :=
  ⟨fun n => ENNReal.ofReal (powerUnitProbability s W n), by
    apply ENNReal.hasSum_coe.mpr
    have h := (powerUnitProbability_summable hs W).hasSum
    rw [powerUnitProbability_tsum hs W] at h
    simpa using h.toNNReal (fun n => powerUnitProbability_nonneg hs W n)⟩

theorem powerUnitPMF_apply (s : ℝ) (hs : 1 < s) (W n : ℕ) :
    powerUnitPMF s hs W n = ENNReal.ofReal (powerUnitProbability s W n) := rfl

theorem powerUnitPMF_support {s : ℝ} (hs : 1 < s) (W : ℕ) :
    (powerUnitPMF s hs W).support = {n : ℕ | n ≠ 0 ∧ n.Coprime W} := by
  ext n
  rw [PMF.mem_support_iff, powerUnitPMF_apply, ENNReal.ofReal_ne_zero_iff]
  change 0 < powerUnitProbability s W n ↔ n ≠ 0 ∧ n.Coprime W
  by_cases hn : n = 0
  · subst n
    simp [powerUnitProbability, powerUnitWeight_zero hs]
  · have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    by_cases hc : n.Coprime W
    · constructor
      · intro _
        exact ⟨hn, hc⟩
      · intro _
        simp only [powerUnitProbability, powerUnitWeight, if_pos hc]
        exact div_pos (Real.rpow_pos_of_pos hnR _) (powerUnitNormalizer_pos hs W)
    · simp [powerUnitProbability, powerUnitWeight, hc]

theorem powerUnitPMF_map_apply {α : Type*} {s : ℝ} (hs : 1 < s)
    (W : ℕ) (stat : ℕ → α) (b : α) :
    ((powerUnitPMF s hs W).map stat) b = ENNReal.ofReal
      (∑' n : ℕ, if b = stat n then powerUnitProbability s W n else 0) := by
  classical
  have hnonneg : ∀ n : ℕ,
      0 ≤ (if b = stat n then powerUnitProbability s W n else 0) := by
    intro n
    split_ifs
    · exact powerUnitProbability_nonneg hs W n
    · exact le_rfl
  have hsum : Summable (fun n : ℕ =>
      if b = stat n then powerUnitProbability s W n else 0) := by
    apply (powerUnitProbability_summable hs W).of_nonneg_of_le hnonneg
    intro n
    split_ifs
    · exact le_rfl
    · exact powerUnitProbability_nonneg hs W n
  have he : ∀ n : ℕ,
      (if b = stat n then ENNReal.ofReal (powerUnitProbability s W n) else 0) =
      ENNReal.ofReal (if b = stat n then powerUnitProbability s W n else 0) := by
    intro n
    split_ifs <;> simp only [ENNReal.ofReal_zero]
  rw [PMF.map_apply]
  simp only [powerUnitPMF_apply, he]
  exact (ENNReal.ofReal_tsum_of_nonneg hnonneg hsum).symm

theorem powerUnitPMF_map_apply_toReal {α : Type*} {s : ℝ} (hs : 1 < s)
    (W : ℕ) (stat : ℕ → α) (b : α) :
    (((powerUnitPMF s hs W).map stat) b).toReal =
      ∑' n : ℕ, if b = stat n then powerUnitProbability s W n else 0 := by
  classical
  rw [powerUnitPMF_map_apply, ENNReal.toReal_ofReal]
  apply tsum_nonneg
  intro n
  split_ifs
  · exact powerUnitProbability_nonneg hs W n
  · exact le_rfl

end Hindman168
