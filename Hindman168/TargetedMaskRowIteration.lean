import Hindman168.MaskRowFlattening
import Hindman168.MaskColumnChoice
import Hindman168.InitialMaskIndicatorRows

/-!
# Finite symbolic iteration of the actual mask row update

Start from all nonempty subset indicators, choose mask coordinates using
only the fixed tracked support, and track one noninvariant copy at every
step. All rows are ordinary integer polynomials with derived anchors and
pair minors. After q steps there are at most r_0*2^q rows and exactly 2q
fresh formal prime slots. Analytic correlation/error bounds are separate.
-/

namespace Hindman168

open scoped BigOperators Classical

structure TargetedMaskRowStage {m : ℕ} (S : Finset (Fin (m + 1))) where
  primeArity : ℕ
  rowCount : ℕ
  rows : PolynomialRowFamily (MvPolynomial (Fin primeArity) ℤ) rowCount m
  target : Fin rowCount
  target_support : ∀ k, rows.row target k ≠ 0 ↔ k ∈ S

noncomputable def initialTargetedMaskRowStage {m : ℕ}
    (S : Finset (Fin (m + 1))) (hS : S.Nonempty) : TargetedMaskRowStage S where
  primeArity := 0
  rowCount := Fintype.card (NonemptyColumnSubset (m + 1))
  rows := initialMaskRowFamily m
  target := initialMaskRowIndex S hS
  target_support k := by
    rw [initialMaskRowFamily_row]
    exact columnSubsetIndicator_nonzero_iff S k

noncomputable def TargetedMaskRowStage.step {m : ℕ} {S : Finset (Fin (m + 1))}
    (F : TargetedMaskRowStage S) (hS : 2 ≤ S.card) (U : Finset (Fin (m + 1))) :
    TargetedMaskRowStage S := by
  let P := chosenMaskColumnPlan S U hS
  have hi := P.tracked_noninvariant hS (F.rows.row F.target) F.target_support
  exact {
    primeArity := 2 + F.primeArity
    rowCount := Fintype.card (MaskDescendant F.rows P.tag)
    rows := F.rows.flattenedMaskStep P.tag
    target := maskTrackedRowIndex F.rows P.tag F.target hi false
    target_support := fun k => (flattenedMaskStep_tracked_support F.rows P.tag F.target hi false k).trans
      (F.target_support k) }

theorem TargetedMaskRowStage.step_rowCount_le {m : ℕ} {S : Finset (Fin (m + 1))}
    (F : TargetedMaskRowStage S) (hS : 2 ≤ S.card) (U : Finset (Fin (m + 1))) :
    (F.step hS U).rowCount ≤ 2 * F.rowCount :=
  maskDescendant_card_le F.rows (chosenMaskColumnPlan S U hS).tag

theorem TargetedMaskRowStage.step_primeArity {m : ℕ} {S : Finset (Fin (m + 1))}
    (F : TargetedMaskRowStage S) (hS : 2 ≤ S.card) (U : Finset (Fin (m + 1))) :
    (F.step hS U).primeArity = 2 + F.primeArity := rfl

noncomputable def TargetedMaskRowStage.iterate {m : ℕ} {S : Finset (Fin (m + 1))}
    (F : TargetedMaskRowStage S) (hS : 2 ≤ S.card) (masks : List (Finset (Fin (m + 1)))) :
    TargetedMaskRowStage S := masks.foldl (fun stage U => stage.step hS U) F

theorem TargetedMaskRowStage.iterate_rowCount_le {m : ℕ} {S : Finset (Fin (m + 1))}
    (F : TargetedMaskRowStage S) (hS : 2 ≤ S.card) (masks : List (Finset (Fin (m + 1)))) :
    (F.iterate hS masks).rowCount ≤ 2 ^ masks.length * F.rowCount := by
  induction masks generalizing F with
  | nil => simp [iterate]
  | cons U rest ih =>
    change ((F.step hS U).iterate hS rest).rowCount ≤ 2 ^ (rest.length + 1) * F.rowCount
    calc
      _ ≤ 2 ^ rest.length * (F.step hS U).rowCount := ih _
      _ ≤ 2 ^ rest.length * (2 * F.rowCount) := Nat.mul_le_mul_left _ (F.step_rowCount_le hS U)
      _ = _ := by rw [pow_succ]; ring

theorem TargetedMaskRowStage.iterate_primeArity {m : ℕ} {S : Finset (Fin (m + 1))}
    (F : TargetedMaskRowStage S) (hS : 2 ≤ S.card) (masks : List (Finset (Fin (m + 1)))) :
    (F.iterate hS masks).primeArity = 2 * masks.length + F.primeArity := by
  induction masks generalizing F with
  | nil => simp [iterate]
  | cons U rest ih =>
    change ((F.step hS U).iterate hS rest).primeArity = 2 * (rest.length + 1) + F.primeArity
    rw [ih, step_primeArity]
    omega

noncomputable def allNonemptyColumnMasks (m : ℕ) : List (Finset (Fin (m + 1))) :=
  ((Finset.univ : Finset (Fin (m + 1))).powerset.erase ∅).toList

theorem allNonemptyColumnMasks_length (m : ℕ) :
    (allNonemptyColumnMasks m).length = 2 ^ (m + 1) - 1 := by
  have he : (∅ : Finset (Fin (m + 1))) ∈ (Finset.univ : Finset (Fin (m + 1))).powerset := by simp
  rw [allNonemptyColumnMasks, Finset.length_toList, Finset.card_erase_of_mem he,
    Finset.card_powerset, Finset.card_univ, Fintype.card_fin]

noncomputable def fullMaskRowStage {m : ℕ} (S : Finset (Fin (m + 1))) (hS : 2 ≤ S.card) :
    TargetedMaskRowStage S :=
  (initialTargetedMaskRowStage S (Finset.card_pos.mp (by omega))).iterate hS (allNonemptyColumnMasks m)

theorem fullMaskRowStage_rowCount_le {m : ℕ} (S : Finset (Fin (m + 1))) (hS : 2 ≤ S.card) :
    (fullMaskRowStage S hS).rowCount ≤
      (2 ^ (m + 1) - 1) * 2 ^ (2 ^ (m + 1) - 1) := by
  have h := (initialTargetedMaskRowStage S (Finset.card_pos.mp (by omega))).iterate_rowCount_le hS
    (allNonemptyColumnMasks m)
  simpa only [fullMaskRowStage, allNonemptyColumnMasks_length,
    initialTargetedMaskRowStage, nonemptyColumnSubset_card, Nat.mul_comm] using h

theorem fullMaskRowStage_primeArity {m : ℕ} (S : Finset (Fin (m + 1))) (hS : 2 ≤ S.card) :
    (fullMaskRowStage S hS).primeArity = 2 * (2 ^ (m + 1) - 1) := by
  have h := (initialTargetedMaskRowStage S (Finset.card_pos.mp (by omega))).iterate_primeArity hS
    (allNonemptyColumnMasks m)
  simpa only [fullMaskRowStage, allNonemptyColumnMasks_length, initialTargetedMaskRowStage, add_zero] using h

theorem TargetedMaskRowStage.step_rowCount_ge {m : ℕ} {S : Finset (Fin (m + 1))}
    (F : TargetedMaskRowStage S) (hS : 2 ≤ S.card) (U : Finset (Fin (m + 1))) :
    F.rowCount ≤ (F.step hS U).rowCount :=
  maskDescendant_card_ge F.rows (chosenMaskColumnPlan S U hS).tag

theorem TargetedMaskRowStage.iterate_rowCount_ge {m : ℕ} {S : Finset (Fin (m + 1))}
    (F : TargetedMaskRowStage S) (hS : 2 ≤ S.card) (masks : List (Finset (Fin (m + 1)))) :
    F.rowCount ≤ (F.iterate hS masks).rowCount := by
  induction masks generalizing F with
  | nil => simp [iterate]
  | cons U rest ih =>
    change F.rowCount ≤ ((F.step hS U).iterate hS rest).rowCount
    exact (F.step_rowCount_ge hS U).trans (ih _)

theorem allNonemptyColumnMasks_mem {m : ℕ} (U : Finset (Fin (m + 1))) :
    U ∈ allNonemptyColumnMasks m ↔ U.Nonempty := by
  simp [allNonemptyColumnMasks, Finset.nonempty_iff_ne_empty]

theorem allNonemptyColumnMasks_nodup (m : ℕ) : (allNonemptyColumnMasks m).Nodup :=
  Finset.nodup_toList _

theorem fullMaskRowStage_rowCount_ge {m : ℕ} (S : Finset (Fin (m + 1))) (hS : 2 ≤ S.card) :
    2 ≤ (fullMaskRowStage S hS).rowCount := by
  have hi := nonemptyColumnSubset_card_ge S
  have hs := (initialTargetedMaskRowStage S (Finset.card_pos.mp (by omega))).iterate_rowCount_ge hS
    (allNonemptyColumnMasks m)
  exact hS.trans (hi.trans hs)

end Hindman168
