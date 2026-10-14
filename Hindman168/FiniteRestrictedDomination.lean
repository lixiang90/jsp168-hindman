import Hindman168.PredictionMajorantCancellation
import Hindman168.PredictionDualMomentDomination

/-! Signed restricted averages can be dominated on the original supports.
The complement splitting is exact and needs no normalization or positive
event mass. This allows weighted exceptional-domain deletion. -/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

theorem abs_expectation_le_majorant_support {α : Type*} (μ : Mass α) (f g : α → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hfg : ∀ x ∈ μ.support, |f x| ≤ g x) :
    |expectation μ f| ≤ expectation μ g := by
  unfold expectation Finsupp.sum
  calc
    _ ≤ ∑ x ∈ μ.support, |μ x * f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum (fun x hx => by
      rw [abs_mul, abs_of_nonneg (hμ x)]
      exact mul_le_mul_of_nonneg_left (hfg x hx) (hμ x))

end Hindman168.FiniteMass

namespace Hindman168

open scoped Classical
open FiniteMass

theorem conditionalFiniteAverage_abs_domination {α β : Type*} (μ : Mass α)
    (base : α → Mass β) (E : α → Prop) (f g : α → β → ℝ)
    (hμ : ∀ x, 0 ≤ μ x)
    (hb : ∀ x ∈ μ.support, E x → ∀ y, 0 ≤ base x y)
    (hfg : ∀ x ∈ μ.support, E x → ∀ y ∈ (base x).support, |f x y| ≤ g x y) :
    |conditionalFiniteAverage μ base E f| ≤ conditionalFiniteAverage μ base E g := by
  unfold conditionalFiniteAverage
  apply abs_expectation_le_majorant_support _ _ _ hμ
  intro x hx
  by_cases hE : E x
  · simp only [if_pos hE]
    exact abs_expectation_le_majorant_support _ _ _ (hb x hx hE) (hfg x hx hE)
  · simp only [if_neg hE, abs_zero, le_refl]

theorem conditionalFiniteAverage_complement_split {α β : Type*} (μ : Mass α)
    (base : α → Mass β) (E : α → Prop) (f : α → β → ℝ) :
    expectation μ (fun x => expectation (base x) (f x)) =
      conditionalFiniteAverage μ base E f + conditionalFiniteAverage μ base (fun x => ¬ E x) f := by
  unfold conditionalFiniteAverage
  rw [← expectation_add]
  apply congrArg (expectation μ)
  funext x
  by_cases hE : E x <;> simp only [hE, if_true, not_true_eq_false, if_false,
    not_false_eq_true, add_zero, zero_add]

end Hindman168
