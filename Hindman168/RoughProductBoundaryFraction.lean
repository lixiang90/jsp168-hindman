import Hindman168.RoughComplexBoundarySelection

namespace Hindman168
open scoped BigOperators Classical

theorem rough_finite_product_deficit {κ : Type*} (s : Finset κ) (u : κ → ℝ)
    (hu0 : ∀ j ∈ s, 0 ≤ u j) (hu1 : ∀ j ∈ s, u j ≤ 1) :
    1-∏ j ∈ s, u j ≤ ∑ j ∈ s, (1-u j) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have h0 : ∀ j ∈ s, 0 ≤ u j := fun j hj => hu0 j (Finset.mem_insert_of_mem hj)
    have h1 : ∀ j ∈ s, u j ≤ 1 := fun j hj => hu1 j (Finset.mem_insert_of_mem hj)
    have hp : ∏ j ∈ s, u j ≤ 1 := Finset.prod_le_one h0 h1
    have hrest := ih h0 h1
    have ha1 := hu1 a (Finset.mem_insert_self _ _)
    have hmul := mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hp)
    nlinarith

end Hindman168
