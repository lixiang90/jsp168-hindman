import Hindman168.UniformFiniteMass
import Hindman168.FiniteConditionalJoint

namespace Hindman168.FiniteMass
open scoped BigOperators Classical

theorem rough_uniform_fiber_weight_apply {α : Type*} (S T : Finset α) (x : α) :
    ((T.card : ℝ) / S.card) * uniformFinsetMass T x =
      if x ∈ T then (S.card : ℝ)⁻¹ else 0 := by
  rw [uniformFinsetMass, flatMass_apply]
  by_cases hx : x ∈ T
  · simp only [if_pos hx]
    have ht : (T.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr ⟨x, hx⟩).ne'
    rw [div_eq_mul_inv]
    calc
      _ = ((T.card : ℝ) * (T.card : ℝ)⁻¹) * (S.card : ℝ)⁻¹ := by ring
      _ = _ := by rw [mul_inv_cancel₀ ht, one_mul]
  · simp only [if_neg hx, mul_zero]

theorem rough_uniform_finset_fiber_mixture {α ι : Type*} [Fintype ι]
    (S : Finset α) (label : α → ι) :
    uniformFinsetMass S = mixture Finset.univ
      (fun i => ((S.filter (fun x => label x = i)).card : ℝ) / S.card)
      (fun i => uniformFinsetMass (S.filter (fun x => label x = i))) := by
  ext x
  rw [mixture_apply]
  simp_rw [rough_uniform_fiber_weight_apply, Finset.mem_filter]
  by_cases hx : x ∈ S
  · simp [uniformFinsetMass, flatMass_apply, hx]
  · simp [uniformFinsetMass, flatMass_apply, hx]

theorem rough_uniform_fiber_weight_sum {α ι : Type*} [Fintype ι]
    (S : Finset α) (hS : 0 < S.card) (label : α → ι) :
    (∑ i : ι, ((S.filter (fun x => label x = i)).card : ℝ) / S.card) = 1 := by
  have he : ∀ i, ((S.filter (fun x => label x = i)).card : ℝ) / S.card =
      (uniformFinsetMass S).mapDomain label i := by
    intro i
    rw [uniformFinsetMass, flatMass_push_coeff, div_eq_mul_inv]
  simp_rw [he]
  rw [← total_eq_sum _ (Finset.subset_univ _), total_push]
  exact uniformFinsetMass_total S hS

theorem rough_uniform_fiber_expectation {α ι : Type*} [Fintype ι]
    (S : Finset α) (label : α → ι) (f : α → ℝ) :
    expectation (uniformFinsetMass S) f =
      ∑ i : ι, (((S.filter (fun x => label x = i)).card : ℝ) / S.card) *
        expectation (uniformFinsetMass (S.filter (fun x => label x = i))) f := by
  rw [rough_uniform_finset_fiber_mixture S label, expectation_mixture]

end Hindman168.FiniteMass
