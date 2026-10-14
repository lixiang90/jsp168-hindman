import Hindman168.IntervalResidueCount
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! Exact half-open real-endpoint integer windows and uniform residue counts. -/
namespace Hindman168
open scoped Classical

noncomputable def realIntegerIntervalLength (a b : ℝ) : ℕ := (⌈b⌉-⌈a⌉).toNat

noncomputable def realIntervalResidueSet (a b : ℝ) (M r : ℕ) : Finset ℤ :=
  intervalResidueSet ⌈a⌉ (realIntegerIntervalLength a b) M r

theorem real_integer_interval_length_cast (a b : ℝ) (hab : a ≤ b) :
    (realIntegerIntervalLength a b : ℝ) = (⌈b⌉ : ℝ)-(⌈a⌉ : ℝ) := by
  have he : (realIntegerIntervalLength a b : ℤ) = ⌈b⌉-⌈a⌉ :=
    Int.toNat_of_nonneg (sub_nonneg.mpr (Int.ceil_mono hab))
  exact_mod_cast he

theorem real_integer_interval_mem (a b : ℝ) (hab : a ≤ b) (z : ℤ) :
    z ∈ integerWindow ⌈a⌉ (realIntegerIntervalLength a b) ↔ a ≤ (z : ℝ) ∧ (z : ℝ) < b := by
  have he : (realIntegerIntervalLength a b : ℤ) = ⌈b⌉-⌈a⌉ :=
    Int.toNat_of_nonneg (sub_nonneg.mpr (Int.ceil_mono hab))
  simp only [integerWindow, he, add_sub_cancel, Finset.mem_Ico, Int.ceil_le, Int.lt_ceil]

theorem real_integer_interval_length_error (a b : ℝ) (hab : a ≤ b) :
    |(realIntegerIntervalLength a b : ℝ)-(b-a)| < 1 := by
  rw [real_integer_interval_length_cast a b hab, abs_lt]
  constructor <;> linarith [Int.le_ceil a,Int.ceil_lt_add_one a,Int.le_ceil b,Int.ceil_lt_add_one b]

theorem real_interval_residue_mem (a b : ℝ) (hab : a ≤ b) (M r : ℕ) (z : ℤ) :
    z ∈ realIntervalResidueSet a b M r ↔
      a ≤ (z : ℝ) ∧ (z : ℝ) < b ∧ z % (M : ℤ) = (r : ℤ) := by
  simp only [realIntervalResidueSet, intervalResidueSet, Finset.mem_filter,
    real_integer_interval_mem a b hab, and_assoc]

theorem real_interval_residue_count (a b : ℝ) (hab : a ≤ b) (M : ℕ) (hM : 0 < M) (r : Fin M) :
    |((realIntervalResidueSet a b M r.val).card : ℝ)-(b-a)/M| ≤ 1+1/(M : ℝ) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hC := interval_residue_count ⌈a⌉ (realIntegerIntervalLength a b) hM r.isLt
  have hE := (real_integer_interval_length_error a b hab).le
  have hD : |((realIntegerIntervalLength a b : ℝ)-(b-a))/(M : ℝ)| ≤ 1/(M : ℝ) := by
    rw [abs_div, abs_of_pos hMR]
    exact div_le_div_of_nonneg_right hE hMR.le
  have he : ((realIntervalResidueSet a b M r.val).card : ℝ)-(b-a)/M =
      (((realIntervalResidueSet a b M r.val).card : ℝ)-(realIntegerIntervalLength a b : ℝ)/M) +
      ((realIntegerIntervalLength a b : ℝ)-(b-a))/M := by ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hC hD)

end Hindman168
