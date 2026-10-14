import Hindman168.AlignmentFiniteWordBudgets
import Hindman168.MasterParameterFamily
import Mathlib.Data.Nat.GCD.BigOperators

/-! The actual Fin n adding pairs are connected to the original natural
index master scales. No substitute scale family is introduced. -/

namespace Hindman168
open scoped BigOperators Classical

def alignmentNaturalBlock {n : ℕ} (S : Finset (Fin n)) : Finset ℕ := S.image Fin.val

def alignmentNaturalBlockProduct {n : ℕ} (t : Fin n → ℕ) (S : Finset (Fin n)) : ℕ :=
  ∏ j ∈ S, t j

def alignmentIntegerScale {n : ℕ} (w : ℕ) (S : Finset (Fin n)) : ℕ :=
  masterScale (primorial w) w n (alignmentNaturalBlock S)

theorem alignmentNaturalBlock_subset {n : ℕ} (S : Finset (Fin n)) :
    alignmentNaturalBlock S ⊆ Finset.range n := by
  intro j hj
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hj
  exact Finset.mem_range.mpr k.isLt

theorem alignmentNaturalBlock_insert {n : ℕ} (i : Fin n) (S : Finset (Fin n)) :
    alignmentNaturalBlock (insert i S) = insert i.val (alignmentNaturalBlock S) :=
  Finset.image_insert _ _ _

theorem alignmentAddingPair_nat_relation {n : ℕ} {i : Fin n} (e : AlignmentAddingPair n i) :
    Chain.AddsTo (alignmentNaturalBlock e.sourceTail) e.sourcePivot.val
      (alignmentNaturalBlock e.targetTail) i.val := by
  refine ⟨e.source_nonempty.image _, ?_, ?_, e.sourcePivot_before⟩
  · intro p hp c hc
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hc
    exact e.source_before_target p' hp' c' hc'
  · intro c hc
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hc
    exact e.target_before_sourcePivot c' hc'

theorem alignmentIntegerScale_positive {n : ℕ} (w : ℕ) (S : Finset (Fin n)) :
    0 < alignmentIntegerScale w S := Nat.pow_pos (primorial_pos w)

theorem alignmentPair_integer_scale_divisibility {n : ℕ} {i : Fin n}
    (w : ℕ) (e : AlignmentAddingPair n i) :
    alignmentIntegerScale w (alignmentPairTargetBlock e) * (primorial w) ^ w ∣
      alignmentIntegerScale w (alignmentPairSourceBlock e) := by
  have h := adding_block_scale_divisibility (primorial w) w (alignmentAddingPair_nat_relation e)
    (e.target_nonempty.image Fin.val)
    (by rw [← alignmentNaturalBlock_insert]; exact alignmentNaturalBlock_subset _)
    (by rw [← alignmentNaturalBlock_insert]; exact alignmentNaturalBlock_subset _)
  simpa only [alignmentIntegerScale, alignmentPairTargetBlock, alignmentPairSourceBlock,
    alignmentNaturalBlock_insert] using h

theorem alignmentNaturalBlockProduct_coprime {n : ℕ} (t : Fin n → ℕ)
    (S : Finset (Fin n)) (W : ℕ) (hunit : ∀ j ∈ S, Nat.Coprime (t j) W) :
    Nat.Coprime (alignmentNaturalBlockProduct t S) W := by
  induction S using Finset.induction_on with
  | empty => exact Nat.coprime_one_left W
  | @insert j S hj ih =>
    rw [alignmentNaturalBlockProduct, Finset.prod_insert hj]
    exact (hunit j (Finset.mem_insert_self j S)).mul_left
      (ih (fun k hk => hunit k (Finset.mem_insert_of_mem hk)))

end Hindman168
