import Hindman168.FiniteEventMajorization
import Hindman168.FiniteProductExpectations
import Mathlib.Tactic

/-!
# Finite event-to-count estimates for Section 2.5

A single positive-mass alignment event may select different members of a
finite model family at different samples. Calibration failures are removed
by the finite union bound; summing model expectations retains the remaining
mass. These are inequalities, not assumptions of positive weighted counts.
-/

namespace Hindman168
open FiniteMass
open scoped BigOperators Classical

/-- A finite sum of model counts is the expectation of their sum. -/
theorem positivePrincipalSum_expectation {α ι : Type*} [Fintype ι]
    (μ : Mass α) (f : ι → α → ℝ) :
    (∑ q, expectation μ (f q)) = expectation μ (fun x => ∑ q, f q x) := by
  simp only [expectation, Finsupp.sum, Finset.mul_sum]
  exact Finset.sum_comm

/-- The event left after removing all calibration failures loses at most
the sum of their probabilities. -/
theorem positivePrincipalSum_good_event {α ι : Type*} [Fintype ι]
    (μ : Mass α) (hμ : ∀ x, 0 ≤ μ x) (E : α → Prop) (bad : ι → α → Prop) :
    event μ E - ∑ j, event μ (bad j) ≤
      event μ (fun x => E x ∧ ∀ j, ¬ bad j x) := by
  have hcover : event μ E ≤ event μ (fun x =>
      (E x ∧ ∀ j, ¬ bad j x) ∨ ∃ j, bad j x) := by
    apply event_mono μ hμ
    intro x hx
    by_cases hb : ∃ j, bad j x
    · exact Or.inr hb
    · exact Or.inl ⟨hx, by simpa using hb⟩
  have hu := event_union_bound μ Finset.univ bad hμ
  simp only [Finset.mem_univ, true_and] at hu
  have ho := event_or_le_add μ (fun x => E x ∧ ∀ j, ¬ bad j x)
    (fun x => ∃ j, bad j x) hμ
  linarith

/-- Pointwise selection of one large nonnegative model on the good
alignment event gives the required lower bound on the total model count. -/
theorem positivePrincipalSum_model_lower_bound {α ι κ : Type*}
    [Fintype ι] [Fintype κ] (μ : Mass α) (hμ : ∀ x, 0 ≤ μ x)
    (E : α → Prop) (bad : ι → α → Prop) (f : κ → α → ℝ)
    (hf : ∀ q x, 0 ≤ f q x) (t : ℝ) (ht : 0 ≤ t)
    (hselect : ∀ x ∈ μ.support, E x → (∀ j, ¬ bad j x) → ∃ q, t ≤ f q x) :
    t * (event μ E - ∑ j, event μ (bad j)) ≤ ∑ q, expectation μ (f q) := by
  have hg := positivePrincipalSum_good_event μ hμ E bad
  have hl : t * event μ (fun x => E x ∧ ∀ j, ¬ bad j x) ≤
      ∑ q, expectation μ (f q) := by
    rw [positivePrincipalSum_expectation, event_eq_sum _ _ (Finset.Subset.refl _),
      expectation_eq_sum _ _ (Finset.Subset.refl _), Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    by_cases hgood : E x ∧ ∀ j, ¬ bad j x
    · rw [if_pos hgood]
      obtain ⟨q, hq⟩ := hselect x hx hgood.1 hgood.2
      have hsum := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset κ)) => hf j x)
        (Finset.mem_univ q)
      nlinarith [hμ x]
    · rw [if_neg hgood, mul_zero]
      exact mul_nonneg (hμ x) (Finset.sum_nonneg (fun q _ => hf q x))
  exact (mul_le_mul_of_nonneg_left hg ht).trans hl

/-- The prediction error is paid once per count, after summing. -/
theorem positivePrincipalSum_error_transfer {κ : Type*} [Fintype κ]
    (I B : κ → ℝ) (η L : ℝ) (herror : ∀ q, |I q - B q| ≤ η)
    (hmodel : L ≤ ∑ q, B q) : L - (Fintype.card κ : ℝ) * η ≤ ∑ q, I q := by
  have he : (∑ q, B q) ≤ (∑ q, I q) + (Fintype.card κ : ℝ) * η := by
    calc
      _ ≤ ∑ q, (I q + η) := Finset.sum_le_sum (fun q _ => by
        have := (abs_le.mp (herror q)).1
        linarith)
      _ = _ := by simp [Finset.sum_add_distrib]
  linarith

/-- Combining calibration, pointwise alignment, and prediction errors
produces an actual weighted-count lower bound. -/
theorem positivePrincipalSum_actual_lower_bound {α ι κ : Type*}
    [Fintype ι] [Fintype κ] (μ : Mass α) (hμ : ∀ x, 0 ≤ μ x)
    (E : α → Prop) (bad : ι → α → Prop) (f : κ → α → ℝ)
    (hf : ∀ q x, 0 ≤ f q x) (t : ℝ) (ht : 0 ≤ t)
    (hselect : ∀ x ∈ μ.support, E x → (∀ j, ¬ bad j x) → ∃ q, t ≤ f q x)
    (I : κ → ℝ) (η : ℝ) (herror : ∀ q, |I q - expectation μ (f q)| ≤ η) :
    t * (event μ E - ∑ j, event μ (bad j)) - (Fintype.card κ : ℝ) * η ≤ ∑ q, I q :=
  positivePrincipalSum_error_transfer I (fun q => expectation μ (f q)) η _ herror
    (positivePrincipalSum_model_lower_bound μ hμ E bad f hf t ht hselect)

end Hindman168
