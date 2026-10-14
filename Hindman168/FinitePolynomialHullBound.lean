import Hindman168.FiniteConvexPowerExpansion
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Algebra.Polynomial

/-!
# Closed convex hull polynomial correlation bounds

Finite expectations are continuous in the product topology, even when the
ambient domain is infinite. Uniform product bounds therefore pass to the
closed convex hull and then to every fixed polynomial, including constants.
-/

namespace Hindman168.FiniteMass

open Filter
open scoped BigOperators Topology Classical

theorem continuous_power_correlation {α : Type*} (μ : Mass α) (c : α → ℝ) (b : ℕ) :
    Continuous (fun G : α → ℝ => expectation μ (fun x => c x * G x ^ b)) := by
  unfold expectation Finsupp.sum
  fun_prop

theorem closedConvexHull_power_bound {α : Type*} (μ : Mass α) (c : α → ℝ)
    (S : Set (α → ℝ)) (b : ℕ) (δ : ℝ)
    (hprod : ∀ f : Fin b → α → ℝ, (∀ q, f q ∈ S) →
      |expectation μ (fun x => c x * ∏ q, f q x)| ≤ δ)
    {G : α → ℝ} (hG : G ∈ closedConvexHull ℝ S) :
    |expectation μ (fun x => c x * G x ^ b)| ≤ δ := by
  rw [closedConvexHull_eq_closure_convexHull] at hG
  have hclosed : IsClosed {G : α → ℝ |
      |expectation μ (fun x => c x * G x ^ b)| ≤ δ} :=
    isClosed_le (continuous_power_correlation μ c b).abs continuous_const
  exact closure_minimal (fun _ hg => convexHull_power_bound μ c S b δ hprod hg) hclosed hG

noncomputable def polynomialCoefficientSize (P : Polynomial ℝ) : ℝ :=
  ∑ b ∈ P.support, |P.coeff b|

theorem polynomial_correlation_expansion {α : Type*} (μ : Mass α)
    (c G : α → ℝ) (P : Polynomial ℝ) :
    expectation μ (fun x => c x * P.eval (G x)) =
      ∑ b ∈ P.support, P.coeff b * expectation μ (fun x => c x * G x ^ b) := by
  simp_rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.mul_sum]
  rw [expectation_finset_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [← expectation_const_mul]
  apply congrArg (expectation μ)
  funext x
  ring

theorem polynomial_correlation_bound {α : Type*} (μ : Mass α)
    (c G : α → ℝ) (P : Polynomial ℝ) (δ : ℝ)
    (hpow : ∀ b ∈ P.support, |expectation μ (fun x => c x * G x ^ b)| ≤ δ) :
    |expectation μ (fun x => c x * P.eval (G x))| ≤ polynomialCoefficientSize P * δ := by
  rw [polynomial_correlation_expansion]
  calc
    _ ≤ ∑ b ∈ P.support, |P.coeff b * expectation μ (fun x => c x * G x ^ b)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b ∈ P.support, |P.coeff b| * δ := by
      apply Finset.sum_le_sum
      intro b hb
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hpow b hb) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; rfl

theorem uniform_polynomial_closedConvexHull {α : Type*}
    (μ : ℕ → Mass α) (c : ℕ → α → ℝ) (S : ℕ → Set (α → ℝ))
    (hprod : ∀ b : ℕ, ∀ η : ℝ, 0 < η → ∀ᶠ w in atTop,
      ∀ f : Fin b → α → ℝ, (∀ q, f q ∈ S w) →
        |expectation (μ w) (fun x => c w x * ∏ q, f q x)| ≤ η)
    (P : Polynomial ℝ) :
    ∀ η : ℝ, 0 < η → ∀ᶠ w in atTop, ∀ G ∈ closedConvexHull ℝ (S w),
      |expectation (μ w) (fun x => c w x * P.eval (G x))| < η := by
  intro η hη
  let C := polynomialCoefficientSize P
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  let δ := η / (1 + C)
  have hδ : 0 < δ := div_pos hη (by linarith)
  have hbudget : C * δ < η := by
    dsimp only [δ]
    rw [← mul_div_assoc, div_lt_iff₀ (by linarith : 0 < 1 + C)]
    nlinarith
  have hall : ∀ᶠ w in atTop, ∀ b ∈ P.support,
      ∀ f : Fin b → α → ℝ, (∀ q, f q ∈ S w) →
        |expectation (μ w) (fun x => c w x * ∏ q, f q x)| ≤ δ := by
    exact (Filter.eventually_all_finset P.support).mpr (fun b _ => hprod b δ hδ)
  filter_upwards [hall] with w hw
  intro G hG
  exact (polynomial_correlation_bound (μ w) (c w) G P δ
    (fun b hb => closedConvexHull_power_bound (μ w) (c w) (S w) b δ (hw b hb) hG)).trans_lt hbudget

end Hindman168.FiniteMass
