import Hindman168.ScalarNonlinearRationalPeriod
import Mathlib.Data.Int.ModEq

/-! TRUE integer-polynomial rational factor period for ANY two congruent
original integer inputs, including negative differences. -/
namespace Hindman168
open Polynomial

theorem scalar_nonlinear_rational_integer_modEq_period (D M q : ℕ) (a n : ℤ)
    (z : ℕ → ℤ) (hM : 0 < M) (hCong : Int.ModEq ((M*q : ℕ) : ℤ) a n) :
    ∃ k : ℤ, (scalarNonlinearRationalPart D M z).eval (n : ℝ)-
      (scalarNonlinearRationalPart D M z).eval (a : ℝ)=(q : ℝ)*(k : ℝ) := by
  let P := scalarNonlinearIntegerNumerator D z
  have hStep : ((M*q : ℕ) : ℤ) ∣ n-a := Int.modEq_iff_dvd.mp hCong
  obtain ⟨k,hk⟩ := hStep.trans (sub_dvd_eval_sub n a P)
  have he : ((P.eval n : ℤ) : ℝ)-((P.eval a : ℤ) : ℝ)=(M : ℝ)*(q : ℝ)*(k : ℝ) := by exact_mod_cast hk
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  refine ⟨k,?_⟩
  rw [scalar_nonlinear_rational_part_integer_eval,scalar_nonlinear_rational_part_integer_eval,← sub_div]
  change (_-_)/(M : ℝ)=_
  rw [he]
  field_simp

end Hindman168
