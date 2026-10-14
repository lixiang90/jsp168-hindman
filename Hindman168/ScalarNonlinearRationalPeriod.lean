import Hindman168.ScalarNonlinearSmallRationalSplit

/-! ACTUAL integer numerator gives a TRUE denominator/lattice-power period
and actual representatives in ONE fixed finite interval. Unbounded numerator
coefficients are retained and never assumed bounded. -/
namespace Hindman168
open Polynomial
open scoped BigOperators

theorem scalar_nonlinear_rational_nat_eval (D M : ℕ) (z : ℕ → ℤ) (n : ℕ) :
    (scalarNonlinearRationalPart D M z).eval (n : ℝ) =
      (((scalarNonlinearIntegerNumerator D z).eval (n : ℤ) : ℤ) : ℝ)/(M : ℝ) := by
  simpa only [Int.cast_natCast] using scalar_nonlinear_rational_part_integer_eval D M z (n : ℤ)

theorem scalar_nonlinear_rational_progression_period (D M q a t : ℕ) (z : ℕ → ℤ) (hM : 0 < M) :
    ∃ k : ℤ, (scalarNonlinearRationalPart D M z).eval ((a+M*q*t : ℕ) : ℝ)-
      (scalarNonlinearRationalPart D M z).eval (a : ℝ) = (q : ℝ)*(k : ℝ) := by
  let P := scalarNonlinearIntegerNumerator D z
  have hstep : ((M*q : ℕ) : ℤ) ∣ ((a+M*q*t : ℕ) : ℤ)-(a : ℤ) := by
    refine ⟨(t : ℤ),?_⟩
    push_cast
    ring
  have hEval := hstep.trans (sub_dvd_eval_sub ((a+M*q*t : ℕ) : ℤ) (a : ℤ) P)
  obtain ⟨k,hk⟩ := hEval
  have he : ((P.eval ((a+M*q*t : ℕ) : ℤ) : ℤ) : ℝ)-((P.eval (a : ℤ) : ℤ) : ℝ) =
      (M : ℝ)*(q : ℝ)*(k : ℝ) := by exact_mod_cast hk
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  refine ⟨k,?_⟩
  rw [scalar_nonlinear_rational_nat_eval,scalar_nonlinear_rational_nat_eval,← sub_div]
  change (_-_)/(M : ℝ)=_
  rw [he]
  field_simp

theorem scalar_nonlinear_rational_finite_residue (D M q n : ℕ) (z : ℕ → ℤ)
    (hM : 0 < M) (hq : 0 < q) :
    ∃ (m : ℕ) (k : ℤ), m < M*q ∧ (scalarNonlinearRationalPart D M z).eval (n : ℝ) =
      (m : ℝ)/(M : ℝ)+(q : ℝ)*(k : ℝ) := by
  let x := (scalarNonlinearIntegerNumerator D z).eval (n : ℤ)
  let p : ℤ := ((M*q : ℕ) : ℤ)
  have hp : 0 < p := by dsimp only [p]; exact_mod_cast Nat.mul_pos hM hq
  let m := (x%p).toNat
  let k := x/p
  have hr : 0 ≤ x%p := Int.emod_nonneg x hp.ne'
  have hm : (m : ℤ)=x%p := Int.toNat_of_nonneg hr
  have hmp : m < M*q := by
    have hh := Int.emod_lt_of_pos x hp
    rw [← hm] at hh
    dsimp only [p] at hh
    exact_mod_cast hh
  have hx : x=(m : ℤ)+p*k := by
    have he := Int.mul_ediv_add_emod x p
    rw [← hm] at he
    change p*k+(m : ℤ)=x at he
    exact he.symm.trans (add_comm _ _)
  have hxR : (x : ℝ)=(m : ℝ)+(M : ℝ)*(q : ℝ)*(k : ℝ) := by exact_mod_cast hx
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  refine ⟨m,k,hmp,?_⟩
  rw [scalar_nonlinear_rational_nat_eval]
  change (x : ℝ)/(M : ℝ)=_
  rw [hxR]
  field_simp

end Hindman168
