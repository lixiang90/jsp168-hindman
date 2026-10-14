import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Location-independent residue discrepancy of an integer interval

For every integer left endpoint A (including negative endpoints), a
half-open interval with T integer points has residue counts within one
of T/k. The proof uses the exact difference of rational ceilings.
-/

namespace Hindman168

open scoped Classical

def integerWindow (A : ℤ) (T : ℕ) : Finset ℤ := Finset.Ico A (A + T)

theorem integerWindow_card (A : ℤ) (T : ℕ) : (integerWindow A T).card = T := by
  simp [integerWindow, Int.card_Ico]

def intervalResidueSet (A : ℤ) (T k a : ℕ) : Finset ℤ :=
  (integerWindow A T).filter (fun z => z % (k : ℤ) = (a : ℤ))

theorem interval_residue_count_rat (A : ℤ) (T : ℕ) {k a : ℕ}
    (hk : 0 < k) (ha : a < k) :
    |((intervalResidueSet A T k a).card : ℚ) - (T : ℚ) / k| ≤ 1 := by
  have hkZ : (0 : ℤ) < k := by exact_mod_cast hk
  have hkQ : (0 : ℚ) < k := by exact_mod_cast hk
  have haZ : (a : ℤ) < k := by exact_mod_cast ha
  have he := Int.Ico_filter_modEq_card A (A + (T : ℤ)) hkZ (a : ℤ)
  have hs : {z ∈ Finset.Ico A (A + (T : ℤ)) | z ≡ (a : ℤ) [ZMOD (k : ℤ)]} =
      intervalResidueSet A T k a := by
    ext z
    simp only [intervalResidueSet, integerWindow, Finset.mem_filter, Int.ModEq,
      Int.emod_eq_of_lt (Int.natCast_nonneg a) haZ]
  rw [hs] at he
  simp only [Int.cast_add, Int.cast_natCast] at he
  let qA : ℚ := ((A : ℚ) - a) / k
  let qB : ℚ := ((A : ℚ) + T - a) / k
  change ((intervalResidueSet A T k a).card : ℤ) = max (Int.ceil qB - Int.ceil qA) 0 at he
  have hAB : qA ≤ qB := by
    dsimp [qA, qB]
    apply div_le_div_of_nonneg_right _ hkQ.le
    linarith [Nat.cast_nonneg (α := ℚ) T]
  rw [max_eq_left (sub_nonneg.mpr (Int.ceil_mono hAB))] at he
  have heQ := congrArg (fun z : ℤ => (z : ℚ)) he
  simp only [Int.cast_natCast, Int.cast_sub] at heQ
  have hd : qB - qA = (T : ℚ) / k := by dsimp [qA, qB]; ring
  have hAlow := Int.le_ceil qA
  have hAup := Int.ceil_lt_add_one qA
  have hBlow := Int.le_ceil qB
  have hBup := Int.ceil_lt_add_one qB
  rw [heQ, ← hd, abs_le]
  constructor <;> linarith

theorem interval_residue_count (A : ℤ) (T : ℕ) {k a : ℕ}
    (hk : 0 < k) (ha : a < k) :
    |((intervalResidueSet A T k a).card : ℝ) - (T : ℝ) / k| ≤ 1 := by
  have h := interval_residue_count_rat A T hk ha
  have hr : ((|((intervalResidueSet A T k a).card : ℚ) - (T : ℚ) / k| : ℚ) : ℝ) ≤
      ((1 : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at hr
  exact hr

end Hindman168
