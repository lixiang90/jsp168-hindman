import Hindman168.RealIntervalResidueGeometry
import Hindman168.FiniteSequenceFreeze
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite

/-! Exact complex sums over a uniform real mesh and all residue classes. -/
namespace Hindman168
open scoped BigOperators Classical

theorem integer_window_residue_sum (A : ℤ) (T M : ℕ) (hM : 0 < M) (f : ℤ → ℂ) :
    (∑ r : Fin M, ∑ z ∈ intervalResidueSet A T M r.val, f z) =
      ∑ z ∈ integerWindow A T, f z := by
  simp only [intervalResidueSet, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  have he (r : Fin M) : z % (M : ℤ) = (r.val : ℤ) ↔ signedPeriodResidue M hM z = r := by
    rw [← signed_period_residue_cast M hM z]
    constructor
    · intro hh
      apply Fin.ext
      exact_mod_cast hh
    · intro hh
      rw [hh]
  simp only [he]
  simp

theorem integer_ordered_cut_sum (c : ℕ → ℤ) (hc : Monotone c) (N : ℕ) (f : ℤ → ℂ) :
    (∑ i ∈ Finset.range N, ∑ z ∈ Finset.Ico (c i) (c (i+1)), f z) =
      ∑ z ∈ Finset.Ico (c 0) (c N), f z := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    rw [← Finset.sum_union (show Disjoint (Finset.Ico (c 0) (c N)) (Finset.Ico (c N) (c (N+1))) from by
      apply Finset.disjoint_left.mpr
      intro z hz ht
      exact (not_lt_of_ge (Finset.mem_Ico.mp ht).1) (Finset.mem_Ico.mp hz).2)]
    rw [Finset.Ico_union_Ico_eq_Ico (hc (Nat.zero_le N)) (hc (Nat.le_succ N))]

noncomputable def realMeshResidueCell (L : ℝ) (N M : ℕ) (i : Fin N) (r : Fin M) : Finset ℤ :=
  realIntervalResidueSet ((i.val : ℝ)/(N : ℝ)*L) (((i.val : ℝ)+1)/(N : ℝ)*L) M r.val

theorem real_mesh_residue_sum (L : ℝ) (hL : 0 ≤ L) (N M : ℕ) (hN : 0 < N) (hM : 0 < M)
    (f : ℤ → ℂ) :
    (∑ i : Fin N, ∑ r : Fin M, ∑ z ∈ realMeshResidueCell L N M i r, f z) =
      ∑ z ∈ Finset.Ico 0 ⌈L⌉, f z := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let c : ℕ → ℤ := fun k => ⌈(k : ℝ)/(N : ℝ)*L⌉
  have hc : Monotone c := by
    intro a b hab
    apply Int.ceil_mono
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (by exact_mod_cast hab) hNR.le) hL
  have hw (i : Fin N) : integerWindow ⌈(i.val : ℝ)/(N : ℝ)*L⌉
      (realIntegerIntervalLength ((i.val : ℝ)/(N : ℝ)*L) (((i.val : ℝ)+1)/(N : ℝ)*L)) =
      Finset.Ico (c i.val) (c (i.val+1)) := by
    have he : ((realIntegerIntervalLength ((i.val : ℝ)/(N : ℝ)*L)
        (((i.val : ℝ)+1)/(N : ℝ)*L)) : ℤ) = c (i.val+1)-c i.val := by
      unfold realIntegerIntervalLength
      simp only [c, Nat.cast_add, Nat.cast_one] at *
      exact Int.toNat_of_nonneg (sub_nonneg.mpr (by simpa only [Nat.cast_succ] using hc (Nat.le_succ i.val)))
    simp only [integerWindow, he, c, add_sub_cancel]
  simp only [realMeshResidueCell, realIntervalResidueSet]
  simp_rw [integer_window_residue_sum _ _ M hM, hw]
  rw [Fin.sum_univ_eq_sum_range (fun k => ∑ z ∈ Finset.Ico (c k) (c (k+1)), f z)]
  rw [integer_ordered_cut_sum c hc N f]
  simp only [c, Nat.cast_zero, zero_div, zero_mul, Int.ceil_zero, div_self hNR.ne', one_mul]

end Hindman168
