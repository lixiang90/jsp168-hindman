import Mathlib.Data.Option.Basic
import Mathlib.Logic.Function.Basic

namespace Hindman168
open scoped Classical

/-- A label either selects its unique admissible preimage or the zero
branch. This works even when the admissible set is empty. -/
theorem injective_admissible_option_selection {A B : Type*} (label : A → B)
    (hinj : Function.Injective label) (P : A → Prop) :
    ∃ σ : B → Option A,
      (∀ a, P a → σ (label a) = some a) ∧
      (∀ b a, σ b = some a → P a ∧ label a = b) := by
  let σ := fun b => if h : ∃ a, P a ∧ label a = b then some h.choose else none
  refine ⟨σ, ?_, ?_⟩
  · intro a ha
    have hex : ∃ a', P a' ∧ label a' = label a := ⟨a, ha, rfl⟩
    dsimp only [σ]
    rw [dif_pos hex]
    exact congrArg some (hinj hex.choose_spec.2)
  · intro b a hs
    dsimp only [σ] at hs
    by_cases hex : ∃ a', P a' ∧ label a' = b
    · rw [dif_pos hex] at hs
      have he : hex.choose = a := Option.some.inj hs
      exact he ▸ hex.choose_spec
    · rw [dif_neg hex] at hs
      cases hs

theorem admissible_option_selection_none {A B : Type*} (label : A → B)
    (hinj : Function.Injective label) (P : A → Prop) (σ : B → Option A)
    (hs : ∀ b a, σ b = some a → P a ∧ label a = b) (a : A) (ha : ¬ P a) :
    σ (label a) = none := by
  cases he : σ (label a) with
  | none => rfl
  | some a' =>
      obtain ⟨hP, hl⟩ := hs (label a) a' he
      exact False.elim (ha (hinj hl ▸ hP))

end Hindman168
