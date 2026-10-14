import Hindman168.FiniteComplexDenseMean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! A TRUE finite partition of actual complex samples has a NONEMPTY
fiber whose mean norm is at least the original mean norm. Actual cardinal
weights are retained; no phase alignment or equal fiber size is assumed. -/
namespace Hindman168
open scoped BigOperators Classical

theorem finite_complex_fiber_mean_selection {α ι : Type*} [DecidableEq ι]
    (S : Finset α) (hS : S.Nonempty) (label : α → ι) (f : α → ℂ) :
    ∃ i ∈ S.image label, (S.filter (fun a => label a=i)).Nonempty ∧
      ‖finiteComplexSetMean S f‖ ≤ ‖finiteComplexSetMean (S.filter (fun a => label a=i)) f‖ := by
  let W := S.image label
  have hW : W.Nonempty := hS.image label
  obtain ⟨i,hi,hMax⟩ := Finset.exists_max_image W
    (fun j => ‖finiteComplexSetMean (S.filter (fun a => label a=j)) f‖) hW
  have hFiber : (S.filter (fun a => label a=i)).Nonempty := by
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hi
    exact ⟨a,Finset.mem_filter.mpr ⟨ha,he⟩⟩
  have hSum : ∑ a ∈ S, f a=∑ j ∈ W, ∑ a ∈ S.filter (fun a => label a=j), f a := by
    symm
    exact Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image.mpr ⟨a,ha,rfl⟩) f
  have hCards : ∑ j ∈ W, (S.filter (fun a => label a=j)).card=S.card := by
    exact Finset.sum_card_fiberwise_eq_card_filter _ _ _ |>.trans (by
      congr 1
      apply Finset.filter_true_of_mem
      intro a ha
      exact Finset.mem_image.mpr ⟨a,ha,rfl⟩)
  have hFiberBound (j : ι) (hj : j ∈ W) :
      ‖∑ a ∈ S.filter (fun a => label a=j), f a‖ ≤
        ((S.filter (fun a => label a=j)).card : ℝ)*‖finiteComplexSetMean (S.filter (fun a => label a=i)) f‖ := by
    rw [← finiteComplexSetMean_mul_card, norm_mul, Complex.norm_natCast,mul_comm]
    exact mul_le_mul_of_nonneg_left (hMax j hj) (Nat.cast_nonneg _)
  have hn : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  refine ⟨i,hi,hFiber,?_⟩
  rw [finiteComplexSetMean,norm_div,Complex.norm_natCast]
  apply (div_le_iff₀ hn).mpr
  rw [hSum]
  calc
    _ ≤ ∑ j ∈ W, ‖∑ a ∈ S.filter (fun a => label a=j), f a‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ W, ((S.filter (fun a => label a=j)).card : ℝ)*
        ‖finiteComplexSetMean (S.filter (fun a => label a=i)) f‖ := Finset.sum_le_sum hFiberBound
    _ = _ := by rw [← Finset.sum_mul,← Nat.cast_sum,hCards,mul_comm]

end Hindman168
