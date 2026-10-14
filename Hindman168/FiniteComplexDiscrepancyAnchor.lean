import Hindman168.FiniteComplexDenseMean
import Mathlib.Data.Finset.Max

/-! A TRUE nonempty finite discrepancy has an actual sample anchor whose
point discrepancy is at least the mean discrepancy. Constant resampling
preserves that discrepancy exactly. -/
namespace Hindman168
open scoped BigOperators Classical

theorem finite_complex_discrepancy_anchor {α : Type*} (S : Finset α) (hS : S.Nonempty)
    (f : α → ℂ) (c : ℂ) :
    ∃ x ∈ S, ‖finiteComplexSetMean S f-c‖ ≤ ‖f x-c‖ := by
  obtain ⟨x,hx,hMax⟩ := Finset.exists_max_image S (fun x => ‖f x-c‖) hS
  exact ⟨x,hx,finiteComplexSetMean_difference_norm_bound S hS f c ‖f x-c‖ (norm_nonneg _) hMax⟩

theorem finite_complex_set_mean_const_nonempty {α : Type*} (S : Finset α) (hS : S.Nonempty)
    (c : ℂ) : finiteComplexSetMean S (fun _ => c)=c := by
  unfold finiteComplexSetMean
  rw [Finset.sum_const,nsmul_eq_mul]
  exact mul_div_cancel_left₀ c (by exact_mod_cast hS.card_pos.ne')

end Hindman168
