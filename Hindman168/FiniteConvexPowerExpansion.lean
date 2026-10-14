import Hindman168.FiniteCenteredLimitTransfer
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Convex.Combination

/-!
# Powers of finite convex combinations under the original finite mass

The exact independent-index expansion retains every convex coefficient.
The correlation bound is independent of the size of the combination.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

theorem expectation_finset_sum {α ι : Type*} (μ : Mass α) (U : Finset ι)
    (f : ι → α → ℝ) :
    expectation μ (fun x => ∑ i ∈ U, f i x) = ∑ i ∈ U, expectation μ (f i) := by
  simp only [expectation, Finsupp.sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem convex_combination_power_expectation {α ι : Type*} [Fintype ι]
    (μ : Mass α) (c : α → ℝ) (weight : ι → ℝ) (f : ι → α → ℝ) (b : ℕ) :
    expectation μ (fun x => c x * (∑ i, weight i * f i x) ^ b) =
      ∑ tuple : Fin b → ι, (∏ q, weight (tuple q)) *
        expectation μ (fun x => c x * ∏ q, f (tuple q) x) := by
  simp_rw [Fintype.sum_pow, Finset.prod_mul_distrib, Finset.mul_sum]
  rw [expectation_finset_sum]
  apply Finset.sum_congr rfl
  intro tuple _
  rw [← expectation_const_mul]
  apply congrArg (expectation μ)
  funext x
  ring

theorem convex_combination_power_bound {α ι : Type*} [Fintype ι]
    (μ : Mass α) (c : α → ℝ) (weight : ι → ℝ) (f : ι → α → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hs : ∑ i, weight i = 1) (b : ℕ) (δ : ℝ)
    (hprod : ∀ tuple : Fin b → ι,
      |expectation μ (fun x => c x * ∏ q, f (tuple q) x)| ≤ δ) :
    |expectation μ (fun x => c x * (∑ i, weight i * f i x) ^ b)| ≤ δ := by
  rw [convex_combination_power_expectation]
  have htotal : ∑ tuple : Fin b → ι, ∏ q, weight (tuple q) = 1 := by
    rw [← Fintype.sum_pow, hs, one_pow]
  calc
    _ ≤ ∑ tuple : Fin b → ι, |(∏ q, weight (tuple q)) *
        expectation μ (fun x => c x * ∏ q, f (tuple q) x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ tuple : Fin b → ι, (∏ q, weight (tuple q)) * δ := by
      apply Finset.sum_le_sum
      intro tuple _
      have hp : 0 ≤ ∏ q, weight (tuple q) := Finset.prod_nonneg (fun _ _ => hw _)
      rw [abs_mul, abs_of_nonneg hp]
      exact mul_le_mul_of_nonneg_left (hprod tuple) hp
    _ = δ := by rw [← Finset.sum_mul, htotal, one_mul]

theorem convexHull_power_bound {α : Type*} (μ : Mass α) (c : α → ℝ)
    (S : Set (α → ℝ)) (b : ℕ) (δ : ℝ)
    (hprod : ∀ f : Fin b → α → ℝ, (∀ q, f q ∈ S) →
      |expectation μ (fun x => c x * ∏ q, f q x)| ≤ δ)
    {G : α → ℝ} (hG : G ∈ convexHull ℝ S) :
    |expectation μ (fun x => c x * G x ^ b)| ≤ δ := by
  obtain ⟨ι, hι, weight, f, hw, hs, hf, he⟩ := mem_convexHull_iff_exists_fintype.mp hG
  letI := hι
  have hpoint (x : α) : G x = ∑ i, weight i * f i x := by
    have hx := congrFun he x
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hx.symm
  simp_rw [hpoint]
  exact convex_combination_power_bound μ c weight f hw hs b δ
    (fun tuple => hprod (fun q => f (tuple q)) (fun q => hf (tuple q)))

end Hindman168.FiniteMass
