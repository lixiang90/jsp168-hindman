import Hindman168.FiniteComplexSetMean

namespace Hindman168
open scoped BigOperators Classical

theorem finite_complex_mean_unit_factor_transfer {α : Type*} (s : Finset α)
    (f g : α → ℂ) (c : ℂ) (hc : ‖c‖ = 1) (δ ε : ℝ) (hε : 0 ≤ ε)
    (hmean : δ ≤ ‖finiteComplexSetMean s f‖)
    (herr : ∀ a ∈ s, ‖f a-c*g a‖ ≤ ε) :
    δ-ε ≤ ‖finiteComplexSetMean s g‖ := by
  have he : finiteComplexSetMean s (fun a => f a-c*g a) =
      finiteComplexSetMean s f-c*finiteComplexSetMean s g := by
    simp only [finiteComplexSetMean, Finset.sum_sub_distrib, ← Finset.mul_sum,
      sub_div, mul_div_assoc]
  have hb := finiteComplexSetMean_norm_bound s (fun a => f a-c*g a) ε hε herr
  rw [he] at hb
  have ht := norm_add_le (finiteComplexSetMean s f-c*finiteComplexSetMean s g)
    (c*finiteComplexSetMean s g)
  rw [sub_add_cancel, norm_mul, hc, one_mul] at ht
  linarith

end Hindman168
