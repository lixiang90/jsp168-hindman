import Mathlib.Order.Filter.AtTopBot.Basic

/-! Uniform eventual validity from EVERY actual selector. The extension at
initial widths uses a default only until actual valid objects exist; no
validity or analytic data for that default are asserted. -/
namespace Hindman168
open Filter
open scoped Classical

theorem rough_eventual_uniform_of_actual_selectors {α : Type*}
    (defaultValue : α) (V P : ℕ → α → Prop)
    (hV : ∀ᶠ w in atTop, ∃ x, V w x)
    (hselectors : ∀ x : ℕ → α, (∀ᶠ w in atTop, V w (x w)) →
      ∀ᶠ w in atTop, P w (x w)) :
    ∀ᶠ w in atTop, ∀ x, V w x → P w x := by
  let selected : ℕ → α := fun w =>
    if hbad : ∃ x, V w x ∧ ¬ P w x then Classical.choose hbad
    else if hvalid : ∃ x, V w x then Classical.choose hvalid else defaultValue
  have hselectedValid : ∀ᶠ w in atTop, V w (selected w) := by
    filter_upwards [hV] with w hw
    by_cases hbad : ∃ x, V w x ∧ ¬ P w x
    · simpa only [selected,dif_pos hbad] using (Classical.choose_spec hbad).1
    · simpa only [selected,dif_neg hbad,dif_pos hw] using Classical.choose_spec hw
  filter_upwards [hselectors selected hselectedValid] with w hw x hx
  by_contra hn
  have hbad : ∃ y, V w y ∧ ¬ P w y := ⟨x,hx,hn⟩
  have hfail := (Classical.choose_spec hbad).2
  exact hfail (by simpa only [selected,dif_pos hbad] using hw)

end Hindman168
