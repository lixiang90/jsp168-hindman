import Hindman168.FiniteComplexSetMean

namespace Hindman168
open scoped BigOperators Classical

theorem finiteComplexSetMean_comm {α β : Type*} (S : Finset α) (T : Finset β)
    (f : α → β → ℂ) :
    finiteComplexSetMean S (fun x => finiteComplexSetMean T (f x)) =
      finiteComplexSetMean T (fun y => finiteComplexSetMean S (fun x => f x y)) := by
  unfold finiteComplexSetMean
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  rw [Finset.sum_comm]
  ring

theorem finiteComplexSetMean_sub_const {α : Type*} (S : Finset α) (hS : S.Nonempty)
    (f : α → ℂ) (c : ℂ) :
    finiteComplexSetMean S (fun x => f x-c) = finiteComplexSetMean S f-c := by
  unfold finiteComplexSetMean
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, sub_div,
    mul_div_cancel_left₀ c (by exact_mod_cast hS.card_pos.ne')]

theorem finiteComplexSetMean_difference_norm_bound {α : Type*} (S : Finset α)
    (hS : S.Nonempty) (f : α → ℂ) (c : ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ x ∈ S, ‖f x-c‖ ≤ B) : ‖finiteComplexSetMean S f-c‖ ≤ B := by
  rw [← finiteComplexSetMean_sub_const S hS]
  exact finiteComplexSetMean_norm_bound S _ B hB hf

theorem finite_complex_mean_dense_large_values {α : Type*} (S : Finset α)
    (hS : S.Nonempty) (f : α → ℂ) (B δ : ℝ) (hB : 0 < B) (hδ : 0 ≤ δ)
    (hf : ∀ x ∈ S, ‖f x‖ ≤ B)
    (hbad : 3*δ*B/4 ≤ ‖finiteComplexSetMean S f‖) :
    δ/4*(S.card : ℝ) ≤ ((S.filter (fun x => δ*B/2 ≤ ‖f x‖)).card : ℝ) := by
  let T := S.filter (fun x => δ*B/2 ≤ ‖f x‖)
  have hsum : (∑ x ∈ S, ‖f x‖) ≤ (S.card : ℝ)*(δ*B/2)+(T.card : ℝ)*B := by
    calc
      _ ≤ ∑ x ∈ S, (δ*B/2 + if δ*B/2 ≤ ‖f x‖ then B else 0) := by
        apply Finset.sum_le_sum
        intro x hx
        by_cases hp : δ*B/2 ≤ ‖f x‖
        · rw [if_pos hp]
          linarith [hf x hx, mul_nonneg hδ hB.le]
        · rw [if_neg hp, add_zero]
          exact le_of_not_ge hp
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul, T]
  have hc : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hn : ‖finiteComplexSetMean S f‖ ≤ (∑ x ∈ S, ‖f x‖)/(S.card : ℝ) := by
    rw [finiteComplexSetMean, norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (norm_sum_le _ _) hc.le
  have h := (le_div_iff₀ hc).mp (hbad.trans hn)
  have ht : δ/4*(S.card : ℝ)*B ≤ (T.card : ℝ)*B := by nlinarith
  exact (mul_le_mul_iff_left₀ hB).mp ht

end Hindman168
