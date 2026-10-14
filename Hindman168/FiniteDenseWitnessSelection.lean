import Mathlib.Combinatorics.Pigeonhole
import Hindman168.FiniteComplexSetMean

/-! Choose one actual witness from a fixed finite list on a dense subset.
The list precedes all source samples; its cardinality remains explicit. -/
namespace Hindman168
open scoped BigOperators Classical

theorem finite_dense_witness_selection {α β : Type*} (T : Finset α) (hT : T.Nonempty)
    (C : Finset β) (P : α → β → Prop) (hw : ∀ x ∈ T, ∃ c ∈ C, P x c) :
    ∃ c ∈ C, ∃ U : Finset α, U ⊆ T ∧ U.Nonempty ∧
      (T.card : ℝ) ≤ (C.card : ℝ)*(U.card : ℝ) ∧ ∀ x ∈ U, P x c := by
  let label (x : α) : β := if hx : x ∈ T then Classical.choose (hw x hx)
    else Classical.choose (hw (Classical.choose hT) (Classical.choose_spec hT))
  have hlabel : ∀ x ∈ T, label x ∈ C ∧ P x (label x) := by
    intro x hx
    dsimp only [label]
    rw [dif_pos hx]
    exact Classical.choose_spec (hw x hx)
  have hC : C.Nonempty := by
    obtain ⟨x,hx⟩ := hT
    exact ⟨label x,(hlabel x hx).1⟩
  have hsum : (∑ c ∈ C, (T.filter (fun x => label x = c)).card) = T.card := by
    exact (Finset.card_eq_sum_card_fiberwise (fun x hx => (hlabel x hx).1)).symm
  have hex : ∃ c ∈ C, (T.card : ℝ) ≤ (C.card : ℝ)*
      ((T.filter (fun x => label x = c)).card : ℝ) := by
    by_contra h
    push Not at h
    have hs := Finset.sum_lt_sum_of_nonempty hC h
    have he : (∑ c ∈ C, (C.card : ℝ)*((T.filter (fun x => label x = c)).card : ℝ)) =
        (C.card : ℝ)*(T.card : ℝ) := by
      rw [← Finset.mul_sum]
      congr 1
      exact_mod_cast hsum
    rw [he] at hs
    simp only [Finset.sum_const,nsmul_eq_mul] at hs
    linarith
  obtain ⟨c,hc,hcard⟩ := hex
  refine ⟨c,hc,T.filter (fun x => label x = c),Finset.filter_subset _ _,?_,hcard,?_⟩
  · apply Finset.card_pos.mp
    by_contra h
    have he : (T.filter (fun x => label x = c)).card = 0 := by omega
    rw [he,Nat.cast_zero,mul_zero] at hcard
    have hp : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
    linarith
  · intro x hx
    obtain ⟨hxt,hxc⟩ := Finset.mem_filter.mp hx
    simpa only [hxc] using (hlabel x hxt).2

end Hindman168
