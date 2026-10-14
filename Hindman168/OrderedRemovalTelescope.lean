import Hindman168.FiniteComplexSetMean
import Mathlib.Data.Finset.Max

/-! One literal ordered factor-removal chain. Every adjacent difference uses
the SAME set function; the accumulated cost is exactly the original factor
count. Empty tails have zero cost, without invented removal directions. -/
namespace Hindman168
open scoped Classical

def orderedRetainedTail {α : Type*} [LinearOrder α] (T : Finset α) (j : α) : Finset α :=
  T.filter (fun k => j < k)

theorem ordered_retained_tail_subset {α : Type*} [LinearOrder α] (T : Finset α) (j : α) :
    orderedRetainedTail T j ⊆ T := Finset.filter_subset _ _

theorem ordered_retained_tail_excludes {α : Type*} [LinearOrder α] (T : Finset α) (j : α) :
    j ∉ orderedRetainedTail T j := by
  simp only [orderedRetainedTail,Finset.mem_filter,lt_self_iff_false,and_false,not_false_eq_true]

theorem ordered_removal_telescope_le {α : Type*} [LinearOrder α]
    (T : Finset α) (f : Finset α → ℂ) (η : ℝ)
    (hstep : ∀ j ∈ T, ‖f (insert j (orderedRetainedTail T j))-f (orderedRetainedTail T j)‖ ≤ η) :
    ‖f T-f ∅‖ ≤ (T.card : ℝ)*η := by
  revert hstep
  induction T using Finset.induction_on_min with
  | empty => intro _; simp
  | insert a S hmin ih =>
    intro hstep
    have ha : a ∉ S := by intro ha; exact (lt_irrefl a) (hmin a ha)
    have hfirst : orderedRetainedTail (insert a S) a=S := by
      rw [orderedRetainedTail,Finset.filter_insert]
      simp only [lt_self_iff_false,if_false]
      exact Finset.filter_eq_self.mpr hmin
    have hrest (j : α) (hj : j ∈ S) : orderedRetainedTail (insert a S) j=orderedRetainedTail S j := by
      simp only [orderedRetainedTail,Finset.filter_insert,if_neg (not_lt_of_ge (hmin j hj).le)]
    have hhead := hstep a (Finset.mem_insert_self a S)
    rw [hfirst] at hhead
    have htail := ih (fun j hj => by
      have hh := hstep j (Finset.mem_insert_of_mem hj)
      rw [hrest j hj] at hh
      exact hh)
    have he : f (insert a S)-f ∅=(f (insert a S)-f S)+(f S-f ∅) := by ring
    rw [he,Finset.card_insert_of_notMem ha,Nat.cast_add,Nat.cast_one]
    have hh := (norm_add_le (f (insert a S)-f S) (f S-f ∅)).trans (add_le_add hhead htail)
    nlinarith

end Hindman168
