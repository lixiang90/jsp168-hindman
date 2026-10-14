import Hindman168.ScalarNonlinearSmallRationalSplit
import Hindman168.ModOneNaturalMultiplier

/-! Genuine real error and integer rational-factor coefficients transfer ALL
positive original monomial bounds. One common natural multiplier is retained;
no smallness of an individual summand is inferred from a circle-norm bound. -/
namespace Hindman168
open Polynomial

theorem scalar_nonlinear_error_all_positive_coefficients
    (E : ℝ[X]) (j M N : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hDeg : E.natDegree ≤ j) (hOne : E.coeff 1=0)
    (hBound : ∀ i : ℕ, 2 ≤ i → i ≤ j →
      (M : ℝ)*(N : ℝ)^i*|E.coeff i| ≤ A) :
    ∀ i : ℕ, 0 < i → (M : ℝ)*(N : ℝ)^i*|E.coeff i| ≤ A := by
  intro i hi
  by_cases h1 : i=1
  · simp only [h1,hOne,abs_zero,mul_zero]
    exact hA
  · by_cases hij : i ≤ j
    · exact hBound i (by omega) hij
    · rw [coeff_eq_zero_of_natDegree_lt (hDeg.trans_lt (Nat.lt_of_not_ge hij)),abs_zero,mul_zero]
      exact hA

theorem scalar_right_factor_coefficient_transport
    (P K E R : ℝ[X]) (c : ℝ) (r M q N i : ℕ) (AK AE : ℝ)
    (hExact : P=K+C c*E+C c*R)
    (hR : ∃ z : ℤ, ((M*q : ℕ) : ℝ)*(C c*R).coeff i=(z : ℝ))
    (hK : (N : ℝ)^i*‖(((r : ℝ)*K.coeff i : ℝ) : UnitAddCircle)‖ ≤ AK)
    (hE : (M : ℝ)*(N : ℝ)^i*|E.coeff i| ≤ AE) :
    (N : ℝ)^i*‖((((r*(M*q) : ℕ) : ℝ)*P.coeff i : ℝ) : UnitAddCircle)‖ ≤
      ((M*q : ℕ) : ℝ)*AK+(r : ℝ)*(q : ℝ)*|c| * AE := by
  obtain ⟨z,hz⟩ := hR
  have hCoeff : P.coeff i=K.coeff i+c*E.coeff i+(C c*R).coeff i := by
    rw [hExact,coeff_add,coeff_add,coeff_C_mul]
  have hEq : ((r*(M*q) : ℕ) : ℝ)*P.coeff i =
      ((M*q : ℕ) : ℝ)*((r : ℝ)*K.coeff i)+
      ((r*(M*q) : ℕ) : ℝ)*c*E.coeff i+((r : ℤ)*z : ℤ) := by
    rw [hCoeff,Nat.cast_mul,Int.cast_mul,Int.cast_natCast,← hz]
    ring
  have hz0 : ((((r : ℤ)*z : ℤ) : ℝ) : UnitAddCircle)=0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨(r : ℤ)*z,by simp⟩
  have hScaledK : (N : ℝ)^i*‖((((M*q : ℕ) : ℝ)*((r : ℝ)*K.coeff i) : ℝ) : UnitAddCircle)‖ ≤
      ((M*q : ℕ) : ℝ)*AK := by
    calc
      _ ≤ (N : ℝ)^i*(((M*q : ℕ) : ℝ)*‖(((r : ℝ)*K.coeff i : ℝ) : UnitAddCircle)‖) :=
        mul_le_mul_of_nonneg_left (mod_one_natural_multiplier_norm_le _ _) (by positivity)
      _ = ((M*q : ℕ) : ℝ)*((N : ℝ)^i*_) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hK (by positivity)
  have hScaledE : (N : ℝ)^i*‖((((r*(M*q) : ℕ) : ℝ)*c*E.coeff i : ℝ) : UnitAddCircle)‖ ≤
      (r : ℝ)*(q : ℝ)*|c| * AE := by
    calc
      _ ≤ (N : ℝ)^i*|((r*(M*q) : ℕ) : ℝ)*c*E.coeff i| :=
        mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using
          (QuotientAddGroup.norm_mk_le_norm (m := ((r*(M*q) : ℕ) : ℝ)*c*E.coeff i)
            (S := AddSubgroup.zmultiples (1 : ℝ)))) (by positivity)
      _ = ((r : ℝ)*(q : ℝ)*|c|)*((M : ℝ)*(N : ℝ)^i*|E.coeff i|) := by
        simp only [Nat.cast_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg r : (0 : ℝ) ≤ r),
          abs_of_nonneg (Nat.cast_nonneg M : (0 : ℝ) ≤ M),abs_of_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hE (by positivity)
  rw [hEq,AddCircle.coe_add,AddCircle.coe_add,hz0,add_zero]
  have h := mul_le_mul_of_nonneg_left (norm_add_le
    ((((M*q : ℕ) : ℝ)*((r : ℝ)*K.coeff i) : ℝ) : UnitAddCircle)
    ((((r*(M*q) : ℕ) : ℝ)*c*E.coeff i : ℝ) : UnitAddCircle)) (by positivity : 0 ≤ (N : ℝ)^i)
  rw [mul_add] at h
  exact h.trans (add_le_add hScaledK hScaledE)

end Hindman168
