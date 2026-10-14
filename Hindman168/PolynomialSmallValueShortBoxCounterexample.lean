import Hindman168.RoughExactInterpolationModOne
import Mathlib.NumberTheory.Real.Irrational

namespace Hindman168
open Polynomial
open scoped BigOperators Classical

/-- This polynomial is zero at the two actual sampling points 1 and 2. -/
noncomputable def smallValueShortBoxPolynomial : ℝ[X] :=
  C (Real.sqrt 2) * (X-C 1) * (X-C 2)

theorem small_value_short_box_natDegree : smallValueShortBoxPolynomial.natDegree = 2 := by
  rw [smallValueShortBoxPolynomial, mul_assoc, natDegree_C_mul irrational_sqrt_two.ne_zero]
  exact (monic_X_sub_C (1 : ℝ)).natDegree_mul (monic_X_sub_C 2) |>.trans
    (by rw [natDegree_X_sub_C, natDegree_X_sub_C])

theorem small_value_short_box_eval (n : ℤ) (hn : n ∈ Finset.Icc (1 : ℤ) 2) :
    smallValueShortBoxPolynomial.eval (n : ℝ) = 0 := by
  obtain hn | hn : n = 1 ∨ n = 2 := by
    have h := Finset.mem_Icc.mp hn
    omega
  all_goals simp [smallValueShortBoxPolynomial, hn]

theorem small_value_short_box_constant : smallValueShortBoxPolynomial.eval 0 = 2*Real.sqrt 2 := by
  simp only [smallValueShortBoxPolynomial, eval_mul, eval_sub, eval_C, eval_X]
  ring

theorem irrational_natural_mod_one_positive (x : ℝ) (hx : Irrational x)
    (q : ℕ) (hq : 0 < q) : 0 < ‖(((q : ℝ)*x : ℝ) : UnitAddCircle)‖ := by
  apply norm_pos_iff.mpr
  intro hz
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
  have hi := hx.natCast_mul hq.ne'
  apply hi.ne_int k
  simpa only [zsmul_eq_mul, mul_one] using hk.symm

/-- No positive uniform bounded multiplier can make the constant coefficient
O(eps), for arbitrarily small positive eps, despite exact zeros on the box.
This refutes the unrestricted short-box version of the small-value auxiliary
statement; it does not refute the corrected quantitative Leibman theorem. -/
theorem small_value_short_box_no_uniform_multiplier (B : ℕ) (hB : 0 < B) :
    ∃ eps : ℝ, 0 < eps ∧ eps < (1 : ℝ)/40 ∧
      (∀ n ∈ Finset.Icc (1 : ℤ) 2,
        ‖((smallValueShortBoxPolynomial.eval (n : ℝ) : ℝ) : UnitAddCircle)‖ ≤ eps) ∧
      ∀ q : ℕ, 0 < q → q ≤ B →
        (B : ℝ)*eps < ‖(((q : ℝ)*smallValueShortBoxPolynomial.eval 0 : ℝ) : UnitAddCircle)‖ := by
  let w : ℕ → ℝ := fun q => ‖(((q : ℝ)*smallValueShortBoxPolynomial.eval 0 : ℝ) : UnitAddCircle)‖
  have hx : Irrational (smallValueShortBoxPolynomial.eval 0) := by
    rw [small_value_short_box_constant]
    exact irrational_sqrt_two.natCast_mul (by norm_num : (2 : ℕ) ≠ 0)
  have hw : ∀ q ∈ Finset.Icc 1 B, 0 < w q := by
    intro q hq
    exact irrational_natural_mod_one_positive _ hx q (Finset.mem_Icc.mp hq).1
  have hS : (Finset.Icc 1 B).Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hB⟩⟩
  obtain ⟨q₀, hq₀, hmin⟩ := Finset.exists_min_image (Finset.Icc 1 B) w hS
  have hw₀ := hw q₀ hq₀
  let eps : ℝ := min ((1 : ℝ)/80) (w q₀/(2*((B : ℝ)+1)))
  have heps : 0 < eps := by dsimp only [eps]; positivity
  refine ⟨eps, heps, ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  · intro n hn
    rw [small_value_short_box_eval n hn]
    simpa only [AddCircle.coe_zero, norm_zero] using heps.le
  · intro q hq hqB
    have hm : w q₀ ≤ w q := hmin q (Finset.mem_Icc.mpr ⟨hq, hqB⟩)
    have hbound : eps*(2*((B : ℝ)+1)) ≤ w q₀ :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    have hstrict : (B : ℝ)*eps < w q₀ := by nlinarith
    exact hstrict.trans_le hm

end Hindman168
