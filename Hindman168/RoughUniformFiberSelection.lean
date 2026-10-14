import Hindman168.RoughUniformFiberMixture
import Hindman168.RoughConvexPieceSelection
import Hindman168.FiniteWeightedErrors

namespace Hindman168
open FiniteMass
open scoped BigOperators Classical

theorem rough_uniform_finset_test_bound {α : Type*} (S : Finset α) (f : α → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hf : ∀ x ∈ S, |f x| ≤ B) :
    |expectation (uniformFinsetMass S) f| ≤ B := by
  by_cases hS : 0 < S.card
  · have hh := expectation_difference_support_bound (uniformFinsetMass S)
      (uniformFinsetMass_nonneg S) f (fun _ => 0) B
      (fun x hx => by
        simpa only [sub_zero] using hf x (flatMass_support S _ hx))
    have hz : expectation (uniformFinsetMass S) (fun _ => 0) = 0 := by simp [expectation]
    simpa only [hz, sub_zero, uniformFinsetMass_total S hS, one_mul] using hh
  · have hs : S = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos hS)
    have hz : uniformFinsetMass S = 0 := by
      ext x
      simp [uniformFinsetMass, flatMass_apply, hs]
    simpa [hz, expectation] using hB

theorem rough_uniform_fiber_discrepancy_selection {α ι : Type*} [Fintype ι]
    (S T : Finset α) (hS : 0 < S.card) (label : α → ι) (f g : α → ℝ)
    (θ B η : ℝ) (hB : 0 ≤ B) (hg : ∀ x ∈ T, |g x| ≤ B)
    (hgap : θ + B * (∑ i : ι,
      |((S.filter (fun x => label x = i)).card : ℝ) / S.card -
        ((T.filter (fun x => label x = i)).card : ℝ) / T.card|) < η)
    (hbad : η ≤ |expectation (uniformFinsetMass S) f - expectation (uniformFinsetMass T) g|) :
    ∃ i : ι, 0 < (S.filter (fun x => label x = i)).card ∧
      θ < |expectation (uniformFinsetMass (S.filter (fun x => label x = i))) f -
        expectation (uniformFinsetMass (T.filter (fun x => label x = i))) g| := by
  have hb : ∀ i ∈ (Finset.univ : Finset ι),
      |expectation (uniformFinsetMass (T.filter (fun x => label x = i))) g| ≤ B :=
    fun i _ => rough_uniform_finset_test_bound _ g B hB
      (fun x hx => hg x (Finset.mem_filter.mp hx).1)
  have hh := rough_convex_piece_after_reweighting Finset.univ
    (fun i => ((S.filter (fun x => label x = i)).card : ℝ) / S.card)
    (fun i => ((T.filter (fun x => label x = i)).card : ℝ) / T.card)
    (fun i => expectation (uniformFinsetMass (S.filter (fun x => label x = i))) f)
    (fun i => expectation (uniformFinsetMass (T.filter (fun x => label x = i))) g)
    θ B η (fun _ _ => by positivity) (rough_uniform_fiber_weight_sum S hS label) hb hgap
    (by simpa only [← rough_uniform_fiber_expectation] using hbad)
  obtain ⟨i, _, hi, hdiff⟩ := hh
  refine ⟨i, ?_, hdiff⟩
  have hnum : (0 : ℝ) < (S.filter (fun x => label x = i)).card :=
    pos_of_mul_pos_left (by simpa only [div_eq_mul_inv] using hi) (by positivity)
  exact_mod_cast hnum

end Hindman168
