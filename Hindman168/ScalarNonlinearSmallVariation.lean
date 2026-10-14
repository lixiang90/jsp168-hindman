import Hindman168.ScalarNonlinearSmallRationalSplit
import Hindman168.NormalizedNaturalPowerVariation

/-! TRUE removed error polynomial has uniform bounded values and genuine
short-interval variation at original N scale. Smallness comes from a short
interval, not from claiming its total value is small on the whole range. -/
namespace Hindman168
open Polynomial
open scoped BigOperators

theorem scalar_nonlinear_small_variation (E : ℝ[X]) (D M N : ℕ) (B : ℝ)
    (hDegree : E.natDegree ≤ D) (h0 : E.coeff 0=0) (h1 : E.coeff 1=0)
    (hN : 0 < N) (hB : 0 ≤ B)
    (hBounds : ∀ j : ℕ, 2 ≤ j → j ≤ D → (M : ℝ)*(N : ℝ)^j*|E.coeff j| ≤ B)
    (x y L : ℝ) (hL : 0 ≤ L) (hx : |x| ≤ (N : ℝ)) (hy : |y| ≤ (N : ℝ)) (hxy : |x-y| ≤ L) :
    (M : ℝ)*|E.eval x-E.eval y| ≤ ((D+1 : ℕ) : ℝ)^2*B*(L/(N : ℝ)) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have he : E.eval x-E.eval y=∑ j ∈ Finset.range (D+1), E.coeff j*(x^j-y^j) := by
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le hDegree),eval_eq_sum_range' (Nat.lt_succ_of_le hDegree),
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hterm (j : ℕ) (hj : j ∈ Finset.range (D+1)) :
      (M : ℝ)*|E.coeff j*(x^j-y^j)| ≤ (D : ℝ)*(L/(N : ℝ))*B := by
    have hjD : j ≤ D := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    by_cases hj2 : 2 ≤ j
    · rw [abs_mul]
      have hPower := normalized_real_power_variation x y (N : ℝ) L j hn hL hx hy hxy
      have hjR : (j : ℝ) ≤ D := by exact_mod_cast hjD
      calc
        _ ≤ (M : ℝ)*(|E.coeff j| *((j : ℝ)*(L/(N : ℝ))*(N : ℝ)^j)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPower (abs_nonneg _)) (Nat.cast_nonneg M)
        _ = ((j : ℝ)*(L/(N : ℝ)))*((M : ℝ)*(N : ℝ)^j*|E.coeff j|) := by ring
        _ ≤ ((j : ℝ)*(L/(N : ℝ)))*B :=
          mul_le_mul_of_nonneg_left (hBounds j hj2 hjD) (by positivity)
        _ = (j : ℝ)*((L/(N : ℝ))*B) := by ring
        _ ≤ (D : ℝ)*((L/(N : ℝ))*B) := mul_le_mul_of_nonneg_right hjR (by positivity)
        _ = _ := by ring
    · have hzero : E.coeff j=0 := by
        have heq : j=0 ∨ j=1 := by omega
        rcases heq with rfl | rfl
        · exact h0
        · exact h1
      rw [hzero,zero_mul,abs_zero,mul_zero]
      positivity
  have hNat : (D+1)*D ≤ (D+1)^2 := by
    rw [pow_two]
    exact Nat.mul_le_mul_left (D+1) (Nat.le_succ D)
  rw [he]
  calc
    _ ≤ (M : ℝ)*(∑ j ∈ Finset.range (D+1), |E.coeff j*(x^j-y^j)|) :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg M)
    _ = ∑ j ∈ Finset.range (D+1), (M : ℝ)*|E.coeff j*(x^j-y^j)| := Finset.mul_sum _ _ _
    _ ≤ ∑ _j ∈ Finset.range (D+1), (D : ℝ)*(L/(N : ℝ))*B := Finset.sum_le_sum hterm
    _ = (((D+1)*D : ℕ) : ℝ)*(B*(L/(N : ℝ))) := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      push_cast
      ring
    _ ≤ (((D+1)^2 : ℕ) : ℝ)*(B*(L/(N : ℝ))) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hNat) (by positivity)
    _ = _ := by push_cast; ring

theorem scalar_nonlinear_small_value_bound (E : ℝ[X]) (D M N : ℕ) (B : ℝ)
    (hDegree : E.natDegree ≤ D) (h0 : E.coeff 0=0) (h1 : E.coeff 1=0)
    (hM : 0 < M) (hN : 0 < N) (hB : 0 ≤ B)
    (hBounds : ∀ j : ℕ, 2 ≤ j → j ≤ D → (M : ℝ)*(N : ℝ)^j*|E.coeff j| ≤ B)
    (x : ℝ) (hx : |x| ≤ (N : ℝ)) : |E.eval x| ≤ ((D+1 : ℕ) : ℝ)^2*B := by
  have hh := scalar_nonlinear_small_variation E D M N B hDegree h0 h1 hN hB hBounds
    x 0 (N : ℝ) (Nat.cast_nonneg N) hx (by simpa only [abs_zero] using Nat.cast_nonneg N)
    (by simpa only [sub_zero] using hx)
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have he : E.eval 0=0 := by simpa only [coeff_zero_eq_eval_zero] using h0
  rw [he,sub_zero,div_self hn,mul_one] at hh
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
  exact (le_mul_of_one_le_left (abs_nonneg _) hm).trans hh

end Hindman168
