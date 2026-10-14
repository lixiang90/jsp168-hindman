import Hindman168.ScalarTaylorTailNorm

/-! Actual P(1)-P_1 is controlled by PROVED higher diagonal coefficients
when P(0)=0. All integer weights and original scales are retained. -/
namespace Hindman168
open Polynomial
open scoped BigOperators Classical

theorem scalar_polynomial_value_one_remainder (P : ℝ[X]) (D : ℕ) (hP : P.natDegree ≤ D)
    (hD : 1 ≤ D) (hZero : P.eval 0=0) :
    P.eval 1-P.coeff 1 = ∑ j ∈ (Finset.range (D+1)).filter (fun j => 2 ≤ j), P.coeff j := by
  have h0 : P.coeff 0=0 := (coeff_zero_eq_eval_zero P).trans hZero
  have hsum : P.eval 1 = ∑ j ∈ Finset.range (D+1), P.coeff j := by
    conv_lhs => rw [P.as_sum_range' (D+1) (by omega)]
    simp only [eval_finsetSum,eval_monomial,one_pow,mul_one]
  have hm : 1 ∈ Finset.range (D+1) := Finset.mem_range.mpr (by omega)
  rw [← Finset.sum_erase_add _ _ hm] at hsum
  have ht : (∑ j ∈ (Finset.range (D+1)).erase 1, P.coeff j) =
      ∑ j ∈ (Finset.range (D+1)).filter (fun j => 2 ≤ j), P.coeff j := by
    symm
    apply Finset.sum_subset
    · intro j hj
      obtain ⟨hjR,hj2⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_erase.mpr ⟨by omega,hjR⟩
    · intro j hj hnot
      obtain ⟨hj1,hjR⟩ := Finset.mem_erase.mp hj
      have hj0 : j=0 := by
        by_contra hn
        apply hnot
        exact Finset.mem_filter.mpr ⟨hjR,by omega⟩
      rw [hj0,h0]
  rw [ht] at hsum
  linarith

theorem scalar_polynomial_value_one_remainder_bound (P : ℝ[X]) (D M N : ℕ) (B : ℝ)
    (hP : P.natDegree ≤ D) (hD : 1 ≤ D) (hZero : P.eval 0=0) (hN : 0 < N) (hB : 0 ≤ B)
    (hHigher : ∀ j : ℕ, 2 ≤ j → j ≤ D →
      (N : ℝ)^j*‖(((M : ℝ)*P.coeff j : ℝ) : UnitAddCircle)‖ ≤ B) :
    (N : ℝ)*‖(((M : ℝ)*(P.eval 1-P.coeff 1) : ℝ) : UnitAddCircle)‖ ≤ (D+1 : ℕ)*B := by
  rw [scalar_polynomial_value_one_remainder P D hP hD hZero,Finset.mul_sum]
  let S := (Finset.range (D+1)).filter (fun j => 2 ≤ j)
  let v : ℕ → ℝ := fun j => (M : ℝ)*P.coeff j
  have hn := integer_weighted_mod_one_norm_bound S (fun _ => (1 : ℤ)) v
  simp only [Int.cast_one,one_mul,abs_one] at hn
  apply (mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg (α := ℝ) N)).trans
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ _j ∈ S, B := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hjR,hj2⟩ := Finset.mem_filter.mp hj
      have hjD : j ≤ D := by have := Finset.mem_range.mp hjR; omega
      have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hpow : (N : ℝ) ≤ (N : ℝ)^j := by
        simpa only [pow_one] using pow_le_pow_right₀ hNr (show 1 ≤ j from by omega)
      exact (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans (hHigher j hj2 hjD)
    _ = (S.card : ℝ)*B := by simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range (D+1))) hB

end Hindman168
