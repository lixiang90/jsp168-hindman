import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Real.Basic

open scoped BigOperators
namespace OAI

theorem real_prod_le_prod_of_injective {α β : Type*} [DecidableEq β]
    {s : Finset α} {t : Finset β} {f : α → ℝ} {g : β → ℝ}
    (e : α → β) (hinj : Set.InjOn e s) (himage : s.image e ⊆ t)
    (hfg : ∀ a ∈ s, f a ≤ g (e a)) (hf : ∀ a ∈ s, 0 ≤ f a)
    (hg : ∀ b ∈ t, b ∉ s.image e → 1 ≤ g b) :
    (∏ a ∈ s, f a) ≤ ∏ b ∈ t, g b := by
  calc
    _ ≤ ∏ a ∈ s, g (e a) := Finset.prod_le_prod hf hfg
    _ = ∏ b ∈ s.image e, g b := (Finset.prod_image hinj).symm
    _ ≤ ∏ b ∈ t, g b := by
      apply Finset.prod_le_prod_of_subset_of_one_le himage
      · intro b hb
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
        exact (hf a ha).trans (hfg a ha)
      · exact hg

end OAI
