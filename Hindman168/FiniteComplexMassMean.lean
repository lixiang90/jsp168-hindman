import Hindman168.UniformFiniteMass
import Hindman168.FiniteComplexSetMean

namespace Hindman168.FiniteMass
open scoped BigOperators Classical

noncomputable def complexExpectation {α : Type*} (μ : Mass α) (f : α → ℂ) : ℂ :=
  μ.sum (fun x a => (a : ℂ) * f x)

theorem complexExpectation_eq_sum {α : Type*} (μ : Mass α) (f : α → ℂ)
    {S : Finset α} (hS : μ.support ⊆ S) :
    complexExpectation μ f = ∑ x ∈ S, (μ x : ℂ) * f x :=
  Finsupp.sum_of_support_subset μ hS _ (by intros; simp)

theorem complexExpectation_sub {α : Type*} (μ ν : Mass α) (f : α → ℂ) :
    complexExpectation (μ - ν) f = complexExpectation μ f - complexExpectation ν f := by
  exact Finsupp.sum_sub_index (fun _ a b => by rw [Complex.ofReal_sub, sub_mul])

theorem complexExpectation_difference_bound {α : Type*} (μ ν : Mass α) (f : α → ℂ)
    (B : ℝ) (hf : ∀ x, ‖f x‖ ≤ B) :
    ‖complexExpectation μ f - complexExpectation ν f‖ ≤ B * distance μ ν := by
  rw [← complexExpectation_sub]
  unfold complexExpectation distance variation Finsupp.sum
  calc
    _ ≤ ∑ x ∈ (μ - ν).support, ‖((μ - ν) x : ℂ) * f x‖ := norm_sum_le _ _
    _ ≤ ∑ x ∈ (μ - ν).support, |(μ - ν) x| * B := by
      apply Finset.sum_le_sum
      intro x _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hf x) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

theorem complexExpectation_uniformFinset {α : Type*} (S : Finset α) (f : α → ℂ) :
    complexExpectation (uniformFinsetMass S) f = finiteComplexSetMean S f := by
  have hsup : (uniformFinsetMass S).support ⊆ S := flatMass_support S _
  rw [complexExpectation_eq_sum _ _ hsup]
  unfold finiteComplexSetMean
  rw [div_eq_mul_inv, mul_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [uniformFinsetMass, flatMass_apply, if_pos hx,
    Complex.ofReal_inv, Complex.ofReal_natCast]

theorem complexExpectation_sign_difference {α : Type*} (μ ν : Mass α) :
    complexExpectation μ (fun x => if ν x ≤ μ x then 1 else -1) -
      complexExpectation ν (fun x => if ν x ≤ μ x then 1 else -1) = (distance μ ν : ℂ) := by
  rw [← complexExpectation_sub]
  unfold complexExpectation distance variation Finsupp.sum
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Finsupp.sub_apply]
  by_cases hx : ν x ≤ μ x
  · rw [if_pos hx, mul_one, abs_of_nonneg (sub_nonneg.mpr hx)]
  · rw [if_neg hx, mul_neg_one, abs_of_neg (sub_neg.mpr (lt_of_not_ge hx)), Complex.ofReal_neg]

theorem uniformFinsetMass_distance_bound {α : Type*} [DecidableEq α] (S T : Finset α) (hS : S.Nonempty) :
    distance (uniformFinsetMass S) (uniformFinsetMass T) ≤
      2 * (((S \ T).card : ℝ) + (T \ S).card) / S.card := by
  let f : α → ℂ := fun x => if uniformFinsetMass T x ≤ uniformFinsetMass S x then 1 else -1
  have hf : ∀ x, ‖f x‖ ≤ (1 : ℝ) := by intro x; dsimp [f]; split_ifs <;> simp
  have h := finiteComplexSetMean_difference_bound S T hS f 1 zero_le_one hf
  rw [← complexExpectation_uniformFinset S, ← complexExpectation_uniformFinset T] at h
  change ‖complexExpectation (uniformFinsetMass S) _ - complexExpectation (uniformFinsetMass T) _‖ ≤ _ at h
  rw [complexExpectation_sign_difference, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ distance (uniformFinsetMass S) (uniformFinsetMass T) from
      variation_nonneg _)] at h
  simpa only [mul_one] using h

end Hindman168.FiniteMass
