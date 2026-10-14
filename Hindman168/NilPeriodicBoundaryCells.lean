import Hindman168.IntervalResidueCount
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Hindman168.NilPieceCubeGeometry

/-! Periodic residue counts in a complete interval cell and its end
strips. The original period q is retained in the relative discrepancy;
no periodic mass is normalized independently in each cell. -/

namespace Hindman168
open scoped BigOperators Classical

noncomputable def periodicCellCount (A : ℤ) (T q : ℕ) (U : Finset ℕ) : ℝ :=
  ∑ a ∈ U, ((intervalResidueSet A T q a).card : ℝ)

def periodicCellWindow (A : ℤ) (T q : ℕ) (U : Finset ℕ) : Finset ℤ :=
  U.biUnion (fun a => intervalResidueSet A T q a)

theorem periodicCellWindow_mem_iff (A : ℤ) (T q : ℕ) (U : Finset ℕ) (y : ℤ) :
    y ∈ periodicCellWindow A T q U ↔
      y ∈ integerWindow A T ∧ ∃ a ∈ U, y % (q : ℤ) = (a : ℤ) := by
  simp only [periodicCellWindow, Finset.mem_biUnion, intervalResidueSet, Finset.mem_filter]
  constructor
  · rintro ⟨a, ha, hy, heq⟩
    exact ⟨hy, a, ha, heq⟩
  · rintro ⟨hy, a, ha, heq⟩
    exact ⟨a, ha, hy, heq⟩

theorem periodicCellCount_eq_card (A : ℤ) (T q : ℕ) (U : Finset ℕ) :
    periodicCellCount A T q U = ((periodicCellWindow A T q U).card : ℝ) := by
  have hd : (↑U : Set ℕ).PairwiseDisjoint (fun a => intervalResidueSet A T q a) := by
    intro a _ b _ hab
    apply Finset.disjoint_left.mpr
    intro y hya hyb
    apply hab
    exact_mod_cast ((Finset.mem_filter.mp hya).2.symm.trans (Finset.mem_filter.mp hyb).2)
  rw [periodicCellWindow, Finset.card_biUnion hd, Nat.cast_sum]
  rfl

theorem periodicCellCount_nonneg (A : ℤ) (T q : ℕ) (U : Finset ℕ) :
    0 ≤ periodicCellCount A T q U := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

theorem periodicCellCount_discrepancy (A : ℤ) (T q : ℕ) (hq : 0 < q)
    (U : Finset ℕ) (hU : U ⊆ Finset.range q) :
    |periodicCellCount A T q U - (U.card : ℝ) * T / q| ≤ U.card := by
  have hc : (∑ _a ∈ U, (T : ℝ) / q) = (U.card : ℝ) * T / q := by simp [mul_div_assoc]
  rw [← hc, periodicCellCount, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a ∈ U, |((intervalResidueSet A T q a).card : ℝ) - (T : ℝ) / q| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ U, (1 : ℝ) := Finset.sum_le_sum (fun a ha => interval_residue_count A T hq (Finset.mem_range.mp (hU ha)))
    _ = (U.card : ℝ) := by simp

theorem periodicCell_end_strips_bound (A : ℤ) (R H q : ℕ) (hR : 0 < R) (hq : 0 < q)
    (U : Finset ℕ) (hU : U ⊆ Finset.range q) :
    periodicCellCount A H q U + periodicCellCount (A + (R : ℤ) - H) H q U ≤
      (2 * (H : ℝ) / R) * periodicCellCount A R q U +
        (U.card : ℝ) * (2 + 2 * (H : ℝ) / R) := by
  have hleft := (abs_le.mp (periodicCellCount_discrepancy A H q hq U hU)).2
  have hright := (abs_le.mp (periodicCellCount_discrepancy (A + (R : ℤ) - H) H q hq U hU)).2
  have hfull := (abs_le.mp (periodicCellCount_discrepancy A R q hq U hU)).1
  have hRr : (0 : ℝ) < R := by exact_mod_cast hR
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hfac : 0 ≤ 2 * (H : ℝ) / R := div_nonneg (by positivity) hRr.le
  have hmul := mul_le_mul_of_nonneg_left hfull hfac
  have heq : (2 * (H : ℝ) / R) * ((U.card : ℝ) * R / q) =
      2 * ((U.card : ℝ) * H / q) := by field_simp
  nlinarith

theorem periodicCell_boundary_count_bound (k : ℤ) (R H q : ℕ) (hR : 0 < R) (hq : 0 < q)
    (U : Finset ℕ) (hU : U ⊆ Finset.range q) :
    (((periodicCellWindow (k * R) R q U).filter
      (fun y => ¬ intervalInteriorRoot R H y)).card : ℝ) ≤
      (2 * (H : ℝ) / R) * periodicCellCount (k * R) R q U +
        (U.card : ℝ) * (2 + 2 * (H : ℝ) / R) := by
  let A : ℤ := k * R
  have hsub : ((periodicCellWindow A R q U).filter (fun y => ¬ intervalInteriorRoot R H y)) ⊆
      periodicCellWindow A H q U ∪ periodicCellWindow (A + (R : ℤ) - H) H q U := by
    intro y hy
    obtain ⟨hwin, hbad⟩ := Finset.mem_filter.mp hy
    obtain ⟨hI, hres⟩ := (periodicCellWindow_mem_iff A R q U y).mp hwin
    have hIy := Finset.mem_Ico.mp hI
    have hRZ : (0 : ℤ) < R := by exact_mod_cast hR
    have hdiv : y / (R : ℤ) = k := (Int.ediv_eq_iff_of_pos hRZ).mpr hIy
    have hrem : y % (R : ℤ) = y - A := by
      have h := Int.mul_ediv_add_emod y (R : ℤ)
      rw [hdiv, mul_comm] at h
      dsimp only [A]
      linarith
    have hbad' : ¬ ((H : ℤ) ≤ y - A ∧ y - A + H < R) := by
      simpa only [intervalInteriorRoot, hrem] using hbad
    by_cases hlo : y - A < H
    · apply Finset.mem_union_left
      apply (periodicCellWindow_mem_iff A H q U y).mpr
      exact ⟨Finset.mem_Ico.mpr ⟨hIy.1, by linarith⟩, hres⟩
    · apply Finset.mem_union_right
      apply (periodicCellWindow_mem_iff (A + (R : ℤ) - H) H q U y).mpr
      have hhi : (R : ℤ) ≤ y - A + H := by omega
      refine ⟨Finset.mem_Ico.mpr ⟨by linarith, ?_⟩, hres⟩
      simpa only [sub_add_cancel] using hIy.2
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hr : (((periodicCellWindow A R q U).filter (fun y => ¬ intervalInteriorRoot R H y)).card : ℝ) ≤
      ((periodicCellWindow A H q U).card : ℝ) + ((periodicCellWindow (A + (R : ℤ) - H) H q U).card : ℝ) := by
    exact_mod_cast hc
  rw [← periodicCellCount_eq_card, ← periodicCellCount_eq_card] at hr
  exact hr.trans (periodicCell_end_strips_bound A R H q hR hq U hU)

end Hindman168
