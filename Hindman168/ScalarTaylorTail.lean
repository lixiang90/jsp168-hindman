import Hindman168.ScalarPolynomialIntegerCoefficientRecovery
import Hindman168.ScalarDifferenceSecondCoefficient

/-! Exact actual Taylor tails. No small-component inference is made. -/
namespace Hindman168
open Polynomial
open scoped BigOperators Classical

noncomputable def scalarTaylorTail (Q : ℝ[X]) (D i : ℕ) (h : ℝ) : ℝ :=
  ∑ j ∈ (Finset.range (D+1)).filter (fun j => i < j), Q.coeff j*(j.choose i : ℝ)*h^(j-i)

noncomputable def scalarTaylorHighLinearTail (Q : ℝ[X]) (D : ℕ) (h : ℝ) : ℝ :=
  ∑ j ∈ (Finset.range (D+1)).filter (fun j => 3 ≤ j), Q.coeff j*(j.choose 1 : ℝ)*h^(j-1)

theorem scalar_taylor_coefficient_tail (Q : ℝ[X]) (D i : ℕ) (h : ℝ)
    (hQ : Q.natDegree ≤ D) (hi : i ≤ D) :
    (Q.comp (X+C h)).coeff i-Q.coeff i = scalarTaylorTail Q D i h := by
  have ht := scalar_polynomial_taylor_coefficient_sum Q h D i hQ
  have hm : i ∈ Finset.range (D+1) := Finset.mem_range.mpr (by omega)
  rw [← Finset.sum_erase_add _ _ hm] at ht
  simp only [Nat.choose_self,Nat.cast_one,Nat.sub_self,pow_zero,mul_one] at ht
  have he : (∑ j ∈ (Finset.range (D+1)).erase i, Q.coeff j*(j.choose i : ℝ)*h^(j-i)) =
      scalarTaylorTail Q D i h := by
    dsimp only [scalarTaylorTail]
    symm
    apply Finset.sum_subset
    · intro j hj
      obtain ⟨hjR,hij⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_erase.mpr ⟨by omega,hjR⟩
    · intro j hj hjNot
      obtain ⟨hji,hjR⟩ := Finset.mem_erase.mp hj
      have hjle : j ≤ i := by
        by_contra hn
        exact hjNot (Finset.mem_filter.mpr ⟨hjR,by omega⟩)
      have hjlt : j < i := by omega
      rw [Nat.choose_eq_zero_of_lt hjlt,Nat.cast_zero,mul_zero,zero_mul]
  change (Q.comp (X+C h)).coeff i = _ at ht
  rw [he] at ht
  linarith

theorem scalar_taylor_linear_high_tail (Q : ℝ[X]) (D : ℕ) (h : ℝ)
    (hQ : Q.natDegree ≤ D) (hD : 2 ≤ D) :
    (Q.comp (X+C h)).coeff 1-Q.coeff 1 = 2*Q.coeff 2*h+scalarTaylorHighLinearTail Q D h := by
  rw [scalar_taylor_coefficient_tail Q D 1 h hQ (by omega)]
  have hm : 2 ∈ (Finset.range (D+1)).filter (fun j : ℕ => 1 < j) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by omega⟩
  unfold scalarTaylorTail
  rw [← Finset.sum_erase_add _ _ hm]
  have he : ((Finset.range (D+1)).filter (fun j : ℕ => 1 < j)).erase 2 =
      (Finset.range (D+1)).filter (fun j : ℕ => 3 ≤ j) := by
    ext j
    simp only [Finset.mem_erase,Finset.mem_filter,Finset.mem_range]
    omega
  rw [he]
  dsimp only [scalarTaylorHighLinearTail]
  norm_num
  ring

theorem scalar_difference_coefficient_tail (P Q : ℝ[X]) (D i : ℕ) (h σ : ℝ)
    (hQ : Q.natDegree ≤ D) (hi : i ≤ D) (hi2 : 2 ≤ i) :
    (scalarDifferencePolynomial P Q h σ).coeff i = P.coeff i+scalarTaylorTail Q D i h := by
  rw [scalarDifferencePolynomial,coeff_add,coeff_sub,coeff_add,coeff_C_mul,coeff_X]
  have hne : i ≠ 1 := by omega
  simp only [if_neg (Ne.symm hne),mul_zero,add_zero]
  rw [← scalar_taylor_coefficient_tail Q D i h hQ hi]
  ring

theorem scalar_difference_linear_high_tail (P Q : ℝ[X]) (D : ℕ) (h σ : ℝ)
    (hQ : Q.natDegree ≤ D) (hD : 2 ≤ D) :
    (scalarDifferencePolynomial P Q h σ).coeff 1 =
      P.coeff 1+2*Q.coeff 2*h+σ+scalarTaylorHighLinearTail Q D h := by
  rw [scalarDifferencePolynomial,coeff_add,coeff_sub,coeff_add,coeff_C_mul,coeff_X]
  simp only [ite_true,mul_one]
  have ht := scalar_taylor_linear_high_tail Q D h hQ hD
  linarith

end Hindman168
