import Hindman168.MvCompleteBinomialTransfer
import Hindman168.ScalarMvIntegerCube

/-! All positive coefficients of any ACTUAL degree-bounded polynomial
have one original-scale bound on a fixed bounded positive sample length.
This uses the circle norm bound and treats all above-degree rows as zero. -/
namespace Hindman168
open scoped BigOperators

theorem mv_bounded_length_coefficient {κ : Type*} [Fintype κ]
    (p : MvPolynomial κ ℝ) (d N T : ℕ) (hp : p.totalDegree ≤ d) (hN : 0 < N) (hNT : N ≤ T) :
    ∀ I : κ → ℕ, 0 < (∑ i, I i) →
      (N : ℝ)^(∑ i, I i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I) p : ℝ) : UnitAddCircle)‖ ≤
        ((T^d : ℕ) : ℝ) := by
  intro I _hI
  by_cases hid : (∑ i, I i) ≤ d
  · have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hN.trans_le hNT
    have hPower : (N : ℝ)^(∑ i, I i) ≤ (T : ℝ)^d :=
      (pow_le_pow_left₀ (Nat.cast_nonneg N) (by exact_mod_cast hNT) _).trans
        (pow_le_pow_right₀ hT1 hid)
    have hCircle : ‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I) p : ℝ) : UnitAddCircle)‖ ≤ 1 :=
      (AddCircle.norm_le_half_period (1 : ℝ) (x :=
        ((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I) p : ℝ) : UnitAddCircle)) (by norm_num)).trans (by norm_num)
    calc
      _ ≤ (N : ℝ)^(∑ i, I i)*1 := mul_le_mul_of_nonneg_left hCircle (by positivity)
      _ ≤ ((T^d : ℕ) : ℝ) := by simpa only [mul_one,Nat.cast_pow] using hPower
  · rw [scalar_mv_coefficient_zero_above_degree p d hp I (Nat.lt_of_not_ge hid),
      AddCircle.coe_zero,norm_zero,mul_zero]
    positivity

end Hindman168
