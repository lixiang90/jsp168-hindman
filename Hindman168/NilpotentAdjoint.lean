import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.RingTheory.Nilpotent.Exp

/-! A finite Hadamard formula in every associative rational algebra. The
adjoint operator is the actual difference of left and right multiplication;
its exponential is computed from commuting nilpotent operators. No BCH
identity or Lie-group adjoint correspondence is assumed. -/

namespace Hindman168
open Module

variable {A : Type*} [Ring A] [Algebra ℚ A]

 def commutatorEndQ (x : A) : End ℚ A := LinearMap.mulLeft ℚ x - LinearMap.mulRight ℚ x

 theorem commutatorEndQ_apply (x y : A) : commutatorEndQ x y = x * y - y * x := rfl

 theorem nilpotent_mulLeftQ {x : A} (hx : IsNilpotent x) :
    IsNilpotent (LinearMap.mulLeft ℚ x) := by
  obtain ⟨k, hk⟩ := hx
  refine ⟨k, ?_⟩
  rw [LinearMap.pow_mulLeft, hk]
  ext y
  exact zero_mul y

 theorem nilpotent_mulRightQ {x : A} (hx : IsNilpotent x) :
    IsNilpotent (LinearMap.mulRight ℚ x) := by
  obtain ⟨k, hk⟩ := hx
  refine ⟨k, ?_⟩
  rw [LinearMap.pow_mulRight, hk]
  ext y
  exact mul_zero y

 theorem mulLeftQ_commute_mulRightQ (x : A) :
    Commute (LinearMap.mulLeft ℚ x) (LinearMap.mulRight ℚ x) := by
  ext y
  exact (mul_assoc x y x).symm

 theorem commutatorEndQ_nilpotent {x : A} (hx : IsNilpotent x) :
    IsNilpotent (commutatorEndQ x) :=
  (mulLeftQ_commute_mulRightQ x).isNilpotent_sub (nilpotent_mulLeftQ hx) (nilpotent_mulRightQ hx)

 theorem exp_mulLeftQ_apply {x : A} (hx : IsNilpotent x) (y : A) :
    IsNilpotent.exp (LinearMap.mulLeft ℚ x) y = IsNilpotent.exp x * y := by
  obtain ⟨k, hk⟩ := hx
  have hL : LinearMap.mulLeft ℚ x ^ k = 0 := by
    rw [LinearMap.pow_mulLeft, hk]
    ext z
    exact zero_mul z
  rw [IsNilpotent.exp_eq_sum hL, IsNilpotent.exp_eq_sum hk]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.pow_mulLeft,
    LinearMap.mulLeft_apply, Finset.sum_mul, smul_mul_assoc]

 theorem exp_mulRightQ_apply {x : A} (hx : IsNilpotent x) (y : A) :
    IsNilpotent.exp (LinearMap.mulRight ℚ x) y = y * IsNilpotent.exp x := by
  obtain ⟨k, hk⟩ := hx
  have hR : LinearMap.mulRight ℚ x ^ k = 0 := by
    rw [LinearMap.pow_mulRight, hk]
    ext z
    exact mul_zero z
  rw [IsNilpotent.exp_eq_sum hR, IsNilpotent.exp_eq_sum hk]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.pow_mulRight,
    LinearMap.mulRight_apply, Finset.mul_sum, mul_smul_comm]

 theorem exp_commutatorEndQ_apply {x : A} (hx : IsNilpotent x) (y : A) :
    IsNilpotent.exp (commutatorEndQ x) y = IsNilpotent.exp x * y * IsNilpotent.exp (-x) := by
  have he : -(LinearMap.mulRight ℚ x) = LinearMap.mulRight ℚ (-x) := by
    ext z
    change -(z * x) = z * (-x)
    rw [mul_neg]
  have hc := (mulLeftQ_commute_mulRightQ x).neg_right
  rw [commutatorEndQ, sub_eq_add_neg, IsNilpotent.exp_add_of_commute hc
    (nilpotent_mulLeftQ hx) (nilpotent_mulRightQ hx).neg]
  change IsNilpotent.exp (LinearMap.mulLeft ℚ x)
    (IsNilpotent.exp (-(LinearMap.mulRight ℚ x)) y) = _
  rw [he, exp_mulLeftQ_apply hx, exp_mulRightQ_apply hx.neg, mul_assoc]

end Hindman168
