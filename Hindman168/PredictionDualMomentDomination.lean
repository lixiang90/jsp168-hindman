import Hindman168.PredictionDualTestExpansion
import Hindman168.FiniteWeightedErrors

/-!
# Absolute dual moments dominated by independent original majorants

Triangle inequalities for nonnegative finite masses replace Jensen here.
Raising the one-copy majorant to a fixed natural power is exactly the
product of independent replicas. No total-mass or moment premise is needed.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

theorem abs_expectation_le_majorant {α : Type*} (μ : Mass α) (f g : α → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hfg : ∀ x, |f x| ≤ g x) :
    |expectation μ f| ≤ expectation μ g := by
  unfold expectation Finsupp.sum
  calc
    _ ≤ ∑ x ∈ μ.support, |μ x * f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum (fun x _ => by
      rw [abs_mul, abs_of_nonneg (hμ x)]
      exact mul_le_mul_of_nonneg_left (hfg x) (hμ x))

end Hindman168.FiniteMass

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

noncomputable def predictionSingleDualTest {α : Type*} (d : ℕ) (μ : Mass α)
    (A : α → Fin d × Bool → ℤ) (T : α → ℕ) (M : α → ℤ)
    (ε : α → ℝ) (g : α → CubeVertex d → ℤ → ℝ) (y : ℤ) : ℝ :=
  expectation μ (fun x => expectation (piMass (fun jb => uniformIntervalMass (A x jb) (T x)))
    (fun u => ε x * ∏ S : CubeVertex d,
      g x S (y + M x * ∑ j ∈ S.val, (u (j, true) - u (j, false)))))

theorem prediction_single_dual_abs_majorant {α : Type*} (d : ℕ) (μ : Mass α)
    (hμ : ∀ x, 0 ≤ μ x) (A : α → Fin d × Bool → ℤ) (T : α → ℕ) (M : α → ℤ)
    (ε : α → ℝ) (hε : ∀ x, |ε x| ≤ 1)
    (g : α → CubeVertex d → ℤ → ℝ) (ν : ℤ → ℝ)
    (hν : ∀ y, 0 ≤ ν y) (hg : ∀ x S y, |g x S y| ≤ 1 + ν y) (y : ℤ) :
    |predictionSingleDualTest d μ A T M ε g y| ≤
      predictionSingleDualTest d μ A T M (fun _ => 1) (fun _ _ y => 1 + ν y) y := by
  unfold predictionSingleDualTest
  apply abs_expectation_le_majorant μ _ _ hμ
  intro x
  apply abs_expectation_le_majorant _ _ _
    (piMass_nonneg _ (fun _ _ => uniformIntervalMass_nonneg _ _ _))
  intro u
  rw [abs_mul, Finset.abs_prod, one_mul]
  have hp : (∏ S : CubeVertex d,
      |g x S (y + M x * ∑ j ∈ S.val, (u (j, true) - u (j, false)))|) ≤
      ∏ S : CubeVertex d,
        (1 + ν (y + M x * ∑ j ∈ S.val, (u (j, true) - u (j, false)))) :=
    Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun S _ => hg x S _)
  have hmaj : 0 ≤ ∏ S : CubeVertex d,
      (1 + ν (y + M x * ∑ j ∈ S.val, (u (j, true) - u (j, false)))) :=
    Finset.prod_nonneg (fun _ _ => add_nonneg zero_le_one (hν _))
  exact (mul_le_mul_of_nonneg_left hp (abs_nonneg _)).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (hε x) hmaj)

theorem prediction_single_dual_majorant_nonneg {α : Type*} (d : ℕ) (μ : Mass α)
    (hμ : ∀ x, 0 ≤ μ x) (A : α → Fin d × Bool → ℤ) (T : α → ℕ) (M : α → ℤ)
    (ν : ℤ → ℝ) (hν : ∀ y, 0 ≤ ν y) (y : ℤ) :
    0 ≤ predictionSingleDualTest d μ A T M (fun _ => 1) (fun _ _ y => 1 + ν y) y := by
  unfold predictionSingleDualTest
  apply expectation_nonneg _ _ hμ
  intro x
  apply expectation_nonneg _ _ (piMass_nonneg _ (fun _ _ => uniformIntervalMass_nonneg _ _ _))
  intro u
  simp only [one_mul]
  exact Finset.prod_nonneg (fun _ _ => add_nonneg zero_le_one (hν _))

theorem prediction_single_dual_power_domination {α : Type*} (d b : ℕ) (μ : Mass α)
    (hμ : ∀ x, 0 ≤ μ x) (A : α → Fin d × Bool → ℤ) (T : α → ℕ) (M : α → ℤ)
    (ε : α → ℝ) (hε : ∀ x, |ε x| ≤ 1)
    (g : α → CubeVertex d → ℤ → ℝ) (ν : ℤ → ℝ)
    (hν : ∀ y, 0 ≤ ν y) (hg : ∀ x S y, |g x S y| ≤ 1 + ν y)
    (ρ : Mass ℤ) (hρ : ∀ y, 0 ≤ ρ y) :
    expectation ρ (fun y => (1 + ν y) * |predictionSingleDualTest d μ A T M ε g y| ^ b) ≤
    expectation ρ (fun y => (1 + ν y) * ∏ _q : Fin b,
      predictionSingleDualTest d μ A T M (fun _ => 1) (fun _ _ y => 1 + ν y) y) := by
  apply expectation_mono _ _ _ hρ
  intro y
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (abs_nonneg _) (prediction_single_dual_abs_majorant d μ hμ A T M ε hε g ν hν hg y) b)
    (by linarith [hν y])

end Hindman168
