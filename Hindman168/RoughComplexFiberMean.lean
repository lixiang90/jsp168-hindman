import Hindman168.RoughUniformFiberMixture
import Hindman168.RoughComplexHaarObstruction

namespace Hindman168
open scoped BigOperators Classical

theorem rough_complex_set_fiber_mean {α ι : Type*} [Fintype ι]
    (S : Finset α) (label : α → ι) (f : α → ℂ) :
    finiteComplexSetMean S f =
      ∑ i : ι, ((((S.filter (fun x => label x = i)).card : ℝ)/S.card : ℝ) : ℂ)*
        finiteComplexSetMean (S.filter (fun x => label x = i)) f := by
  have hi : ∀ i : ι,
      ((((S.filter (fun x => label x = i)).card : ℝ)/S.card : ℝ) : ℂ)*
        finiteComplexSetMean (S.filter (fun x => label x = i)) f =
          (∑ x ∈ S.filter (fun x => label x = i), f x)/(S.card : ℂ) := by
    intro i
    rw [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_natCast,
      div_mul_eq_mul_div, mul_comm ((S.filter (fun x => label x = i)).card : ℂ),
      finiteComplexSetMean_mul_card]
  simp_rw [hi]
  rw [← Finset.sum_div, Finset.sum_fiberwise S label f]
  rfl

theorem rough_complex_fiber_haar_selection {α ι : Type*} [Fintype ι]
    (S : Finset α) (hS : S.Nonempty) (label : α → ι) (f : α → ℂ) (mean : ℂ) :
    ∃ i : ι, (S.filter (fun x => label x = i)).Nonempty ∧
      ‖finiteComplexSetMean S f-mean‖ ≤
        ‖finiteComplexSetMean (S.filter (fun x => label x = i)) f-mean‖ := by
  have h := rough_convex_haar_obstruction Finset.univ
    (fun i => ((S.filter (fun x => label x = i)).card : ℝ)/S.card)
    (fun i => finiteComplexSetMean (S.filter (fun x => label x = i)) f) mean
    (fun _ _ => by positivity)
    (FiniteMass.rough_uniform_fiber_weight_sum S hS.card_pos label)
  obtain ⟨i, _, hi, hgap⟩ := h
  refine ⟨i, Finset.card_pos.mp ?_, ?_⟩
  · have hnum : (0 : ℝ) < (S.filter (fun x => label x = i)).card :=
      pos_of_mul_pos_left (by simpa only [div_eq_mul_inv] using hi) (by positivity)
    exact_mod_cast hnum
  · simpa only [← rough_complex_set_fiber_mean] using hgap

end Hindman168
