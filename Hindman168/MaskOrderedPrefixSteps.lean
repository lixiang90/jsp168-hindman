import Hindman168.MaskOneStepCorrelation
import Mathlib.Data.List.TakeDrop

/-! The actual ordered nonempty masks, their remaining families, and
adjacent prefix stages. No arbitrary ordering or repeated mask is used. -/

namespace Hindman168

open scoped Classical

noncomputable def maskCurrentColumnMask (m : ℕ) (k : Fin (allNonemptyColumnMasks m).length) :
    Finset (Fin (m + 1)) := (allNonemptyColumnMasks m).get k

noncomputable def maskRemainingMasks (m k : ℕ) : Finset (Finset (Fin (m + 1))) :=
  ((allNonemptyColumnMasks m).drop k).toFinset

theorem maskRemainingMasks_zero (m : ℕ) :
    maskRemainingMasks m 0 = (Finset.univ : Finset (Fin (m + 1))).powerset.erase ∅ := by
  simp [maskRemainingMasks, allNonemptyColumnMasks]

theorem maskRemainingMasks_full (m : ℕ) :
    maskRemainingMasks m (allNonemptyColumnMasks m).length = ∅ := by
  simp [maskRemainingMasks]

theorem maskCurrentColumnMask_mem_remaining (m : ℕ) (k : Fin (allNonemptyColumnMasks m).length) :
    maskCurrentColumnMask m k ∈ maskRemainingMasks m k.val := by
  have he := List.cons_get_drop_succ (l := allNonemptyColumnMasks m) (n := k)
  have hs : (allNonemptyColumnMasks m).get k ∈
      (allNonemptyColumnMasks m).get k :: (allNonemptyColumnMasks m).drop (k.val+1) :=
    List.mem_cons_self
  rw [he] at hs
  exact List.mem_toFinset.mpr hs

theorem maskRemainingMasks_succ (m : ℕ) (k : Fin (allNonemptyColumnMasks m).length) :
    maskRemainingMasks m (k.val + 1) =
      (maskRemainingMasks m k.val).erase (maskCurrentColumnMask m k) := by
  have he := List.cons_get_drop_succ (l := allNonemptyColumnMasks m) (n := k)
  have hn : ((allNonemptyColumnMasks m).drop k.val).Nodup :=
    (allNonemptyColumnMasks_nodup m).drop
  rw [← he] at hn
  have hnot : maskCurrentColumnMask m k ∉ ((allNonemptyColumnMasks m).drop (k.val+1)).toFinset := by
    simpa only [maskCurrentColumnMask, List.mem_toFinset] using (List.nodup_cons.mp hn).1
  unfold maskRemainingMasks
  rw [← he, List.toFinset_cons]
  exact (Finset.erase_insert hnot).symm

variable {m : ℕ} (S : Finset (Fin (m + 1))) (hS : 2 ≤ S.card)

theorem maskPrefixRowStage_zero :
    maskPrefixRowStage S hS 0 = initialTargetedMaskRowStage S (Finset.card_pos.mp (by omega)) := by
  simp [maskPrefixRowStage, TargetedMaskRowStage.iterate]

theorem maskPrefixRowStage_succ (k : Fin (allNonemptyColumnMasks m).length) :
    maskPrefixRowStage S hS (k.val + 1) =
      (maskPrefixRowStage S hS k.val).step hS (maskCurrentColumnMask m k) := by
  unfold maskPrefixRowStage
  rw [← List.take_concat_get' (allNonemptyColumnMasks m) k.val k.isLt]
  simp only [TargetedMaskRowStage.iterate, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

theorem maskPrefixRowStage_full :
    maskPrefixRowStage S hS (allNonemptyColumnMasks m).length = fullMaskRowStage S hS := by
  simp [maskPrefixRowStage, fullMaskRowStage]

end Hindman168
