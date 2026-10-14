import Hindman168.FiniteComplexMassMean
import Hindman168.FiniteCoordinateTranslation
import Mathlib.Data.Fintype.BigOperators

namespace Hindman168.FiniteMass
open scoped BigOperators Classical

theorem uniformFinsetMass_pi {ι α : Type*} [Fintype ι] (S : ι → Finset α) :
    uniformFinsetMass (Fintype.piFinset S) = piMass (fun j => uniformFinsetMass (S j)) := by
  ext x
  rw [piMass_apply]
  by_cases hx : ∀ j, x j ∈ S j
  · simp only [uniformFinsetMass, flatMass_apply, if_pos (Fintype.mem_piFinset.mpr hx),
      if_pos (hx _), Fintype.card_piFinset, Nat.cast_prod, Finset.prod_inv_distrib]
  · obtain ⟨j, hj⟩ := not_forall.mp hx
    rw [uniformFinsetMass, flatMass_apply, if_neg (fun h => hj (Fintype.mem_piFinset.mp h j))]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact if_neg hj

theorem uniformBox_distance_bound {ι α : Type*} [Fintype ι] [DecidableEq α] (S T : ι → Finset α)
    (hS : ∀ j, (S j).Nonempty) (hT : ∀ j, (T j).Nonempty) :
    distance (uniformFinsetMass (Fintype.piFinset S)) (uniformFinsetMass (Fintype.piFinset T)) ≤
      ∑ j, 2 * ((((S j) \ (T j)).card : ℝ) + ((T j) \ (S j)).card) / (S j).card := by
  rw [uniformFinsetMass_pi, uniformFinsetMass_pi]
  apply (piMass_probability_distance_fintype _ _
    (fun j => uniformFinsetMass_nonneg (S j)) (fun j => uniformFinsetMass_nonneg (T j))
    (fun j => uniformFinsetMass_total (S j) (hS j).card_pos)
    (fun j => uniformFinsetMass_total (T j) (hT j).card_pos)).trans
  exact Finset.sum_le_sum (fun j _ => uniformFinsetMass_distance_bound (S j) (T j) (hS j))

theorem finiteComplexBoxMean_difference_bound {ι α : Type*} [Fintype ι] [DecidableEq α] (S T : ι → Finset α)
    (hS : ∀ j, (S j).Nonempty) (hT : ∀ j, (T j).Nonempty)
    (f : (ι → α) → ℂ) (B : ℝ) (hB : 0 ≤ B) (hf : ∀ x, ‖f x‖ ≤ B) :
    ‖finiteComplexSetMean (Fintype.piFinset S) f - finiteComplexSetMean (Fintype.piFinset T) f‖ ≤
      B * ∑ j, 2 * ((((S j) \ (T j)).card : ℝ) + ((T j) \ (S j)).card) / (S j).card := by
  rw [← complexExpectation_uniformFinset, ← complexExpectation_uniformFinset]
  exact (complexExpectation_difference_bound _ _ f B hf).trans
    (mul_le_mul_of_nonneg_left (uniformBox_distance_bound S T hS hT) hB)

end Hindman168.FiniteMass
