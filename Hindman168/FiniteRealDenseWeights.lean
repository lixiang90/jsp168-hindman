import Hindman168.FiniteComplexDenseMean

namespace Hindman168
open scoped BigOperators Classical

theorem finite_real_sum_dense_large_weights {α : Type*} (S : Finset α)
    (w : α → ℝ) (B δ : ℝ) (hB : 0 < B) (hδ : 0 ≤ δ)
    (hw : ∀ x ∈ S, w x ≤ B)
    (hsum : δ*(S.card : ℝ)*B ≤ ∑ x ∈ S, w x) :
    δ/2*(S.card : ℝ) ≤ ((S.filter (fun x => δ*B/2 ≤ w x)).card : ℝ) := by
  let T := S.filter (fun x => δ*B/2 ≤ w x)
  have hupper : (∑ x ∈ S, w x) ≤ (S.card : ℝ)*(δ*B/2)+(T.card : ℝ)*B := by
    calc
      _ ≤ ∑ x ∈ S, (δ*B/2 + if δ*B/2 ≤ w x then B else 0) := by
        apply Finset.sum_le_sum
        intro x hx
        by_cases hp : δ*B/2 ≤ w x
        · rw [if_pos hp]
          linarith [hw x hx, mul_nonneg hδ hB.le]
        · rw [if_neg hp, add_zero]
          exact le_of_not_ge hp
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul, T]
  have h : δ/2*(S.card : ℝ)*B ≤ (T.card : ℝ)*B := by linarith
  exact (mul_le_mul_iff_left₀ hB).mp h

end Hindman168
