import Hindman168.MasterCommonTailBudgets

/-!
# Crude sup bounds from actual tail-divisor probability laws

The divisor mask lies between zero and its supported divisor cap.
The centered root and all one-plus-mask-dominated nonroot tests then
have a fixed polynomial sup bound at the original common budget.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

theorem integerDivisorMask_probability_bounds (ρ : Mass ℕ) (K : ℕ)
    (hρ : ∀ k, 0 ≤ ρ k) (ht : total ρ = 1)
    (hK : ∀ k ∈ ρ.support, k ≤ K) (z : ℤ) :
    0 ≤ integerDivisorMask ρ z ∧ integerDivisorMask ρ z ≤ K := by
  unfold integerDivisorMask
  constructor
  · exact Finset.sum_nonneg (fun k _ => mul_nonneg (hρ k) (by split_ifs <;> positivity))
  · calc
      _ ≤ ∑ k ∈ ρ.support, ρ k * (K : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        apply mul_le_mul_of_nonneg_left _ (hρ k)
        split_ifs
        · exact_mod_cast hK k hk
        · exact Nat.cast_nonneg _
      _ = total ρ * (K : ℝ) := by rw [← Finset.sum_mul]; rfl
      _ = _ := by rw [ht, one_mul]

theorem MasterParameterConditions.prediction_masks_eventually_bounded
    {n N m b d : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A D F)
    (C : ℕ → Chain m) (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → ReplicaCubeRow b d → Fin m) (V : ℕ → ℕ)
    (hbudget : ∀ᶠ w in atTop, ∀ base,
      tailBound ((C w).tailCutoffs (F.cutoff w) (label w base)) ≤ V w) :
    ∀ᶠ w in atTop, ∀ base t,
      0 ≤ integerDivisorMask (masterPredictionBaseDivisorMass F C label w base) t ∧
        integerDivisorMask (masterPredictionBaseDivisorMass F C label w base) t ≤ V w := by
  filter_upwards [hF.raw_cutoffs_valid, hbudget] with w hw hb
  intro base t
  let Xs := (C w).tailCutoffs (F.cutoff w) (label w base)
  have hv : ValidCutoffs Xs (primorial w) := chain_tailCutoffs_valid (C w) (F.cutoff w)
    (primorial w) (hN w) (fun j hj => ⟨(hw j hj).1, (hw j hj).2.1⟩) (label w base)
  exact integerDivisorMask_probability_bounds (tailMass (primorial w) Xs) (V w)
    (tailMass_nonneg (primorial_pos w) Xs hv) (tailMass_total (primorial_pos w) Xs hv)
    (fun k hk => ((tailMass_support Xs hv k hk).2.1).trans (hb base)) t

theorem MasterParameterConditions.prediction_tests_eventually_sup_bound
    {n N m r b d h : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A D F)
    (C : ℕ → Chain m) (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → ReplicaCubeRow b d → Fin m) (V : ℕ → ℕ)
    (hV : ∀ᶠ w in atTop, 2 ≤ V w)
    (hbudget : ∀ᶠ w in atTop, ∀ base,
      tailBound ((C w).tailCutoffs (F.cutoff w) (label w base)) ≤ V w)
    (dir : Fin h → Fin b × CubeVertex d) (hdir : Function.Surjective dir)
    (G : ℕ → (Fin r → ℕ) → ReplicaCubeRow b d → ℤ → ℝ)
    (hroot : ∀ w x, G w x none = fun t =>
      integerDivisorMask (masterPredictionBaseDivisorMass F C label w none) t - 1)
    (hG : ∀ᶠ w in atTop, ∀ x i t, |G w x (some (dir i)) t| ≤
      1 + integerDivisorMask (masterPredictionBaseDivisorMass F C label w (some (dir i))) t) :
    ∀ᶠ w in atTop, ∀ x base t, |G w x base t| ≤ (V w : ℝ) ^ 2 := by
  filter_upwards [hF.prediction_masks_eventually_bounded C hN label V hbudget, hV, hG]
    with w hm hv hg
  have hvr : (2 : ℝ) ≤ V w := by exact_mod_cast hv
  have hp : 1 + (V w : ℝ) ≤ (V w : ℝ) ^ 2 := by nlinarith
  intro x base t
  cases base with
  | none =>
    rw [congrFun (hroot w x) t]
    calc
      _ ≤ |integerDivisorMask (masterPredictionBaseDivisorMass F C label w none) t| + |(1 : ℝ)| :=
        abs_sub _ _
      _ ≤ 1 + (V w : ℝ) := by rw [abs_of_nonneg (hm none t).1]; norm_num; linarith [(hm none t).2]
      _ ≤ _ := hp
  | some row =>
    obtain ⟨i, rfl⟩ := hdir row
    calc
      _ ≤ 1 + integerDivisorMask (masterPredictionBaseDivisorMass F C label w (some (dir i))) t := hg x i t
      _ ≤ 1 + (V w : ℝ) := by linarith [(hm (some (dir i)) t).2]
      _ ≤ _ := hp

end Hindman168
