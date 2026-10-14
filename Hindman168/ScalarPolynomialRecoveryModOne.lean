import Hindman168.ScalarPolynomialRecoveryWeights
import Hindman168.IntegerWeightedModOneNorm
import Hindman168.UnitCircleDensePowerInverse

namespace Hindman168
open Polynomial
open scoped BigOperators Classical

/-- Quantitative recovery of original nonconstant modular coefficients from
the actual affine polynomial. The integer weights and true length ratio
preserve the N^-i scale; no modular division or inverse theorem is assumed. -/
theorem scalar_polynomial_recovery_mod_one (p : ℝ[X]) (a q D i N H k : ℕ)
    (hp : p.natDegree ≤ D) (hq : 0 < q) (ha : a ≤ N) (hN : 0 < N)
    (hi : 0 < i) (ρ A : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hA : 0 ≤ A) (hH : ρ*(N : ℝ) ≤ H)
    (hcoeff : ∀ j : ℕ, 0 < j → j ≤ D →
      (H : ℝ)^j*‖(((k : ℝ)*(scalarPolynomialOnProgression p a q).coeff j : ℝ) : UnitAddCircle)‖ ≤ A) :
    (N : ℝ)^i*‖(((k*q^D : ℕ)*p.coeff i : ℝ) : UnitAddCircle)‖ ≤
      (D+1 : ℕ)*(q : ℝ)^D*(2 : ℝ)^D*A/ρ^D := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let v := fun j => (k : ℝ)*(scalarPolynomialOnProgression p a q).coeff j
  have he : ((k*q^D : ℕ) : ℝ)*p.coeff i =
      ∑ j ∈ Finset.range (D+1), (scalarProgressionRecoveryWeight a q D i j : ℝ)*v j := by
    calc
      _ = (k : ℝ)*((q : ℝ)^D*p.coeff i) := by push_cast; ring
      _ = (k : ℝ)*∑ j ∈ Finset.range (D+1),
          (scalarProgressionRecoveryWeight a q D i j : ℝ)*(scalarPolynomialOnProgression p a q).coeff j := by
        rw [scalar_polynomial_integer_coefficient_recovery p a q D i hp]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [v]
        ring
  rw [he]
  have hnorm := integer_weighted_mod_one_norm_bound (Finset.range (D+1))
    (scalarProgressionRecoveryWeight a q D i) v
  have hmul := mul_le_mul_of_nonneg_left hnorm (pow_nonneg hNr.le i)
  refine hmul.trans ?_
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ _j ∈ Finset.range (D+1), ((q : ℝ)^D*(2 : ℝ)^D*A/ρ^D) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjD : j ≤ D := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      by_cases hji : j < i
      · rw [scalar_progression_recovery_weight_zero_below a q D i j hji]
        simp only [Int.cast_zero, abs_zero, zero_mul, mul_zero]
        positivity
      · have hij : i ≤ j := Nat.le_of_not_gt hji
        have hjpos : 0 < j := hi.trans_le hij
        have hs := real_power_bound_from_fractional_length ρ (H : ℝ) (N : ℝ)
          ‖(v j : UnitAddCircle)‖ A j hρ hNr.le (norm_nonneg _) hH (hcoeff j hjpos hjD)
        have hρpow : ρ^D ≤ ρ^j := pow_le_pow_of_le_one hρ.le hρ1 hjD
        have hs' : (N : ℝ)^j*‖(v j : UnitAddCircle)‖ ≤ A/ρ^D :=
          hs.trans (div_le_div_of_nonneg_left hA (pow_pos hρ D) hρpow)
        have hw := scalar_progression_recovery_weight_bound a q D i j N hq ha hjD
        have hwN := mul_le_mul_of_nonneg_left hw (pow_nonneg hNr.le i)
        have hpw : (N : ℝ)^i*(N : ℝ)^(j-i) = (N : ℝ)^j := by
          rw [← pow_add, Nat.add_sub_of_le hij]
        calc
          _ ≤ ((N : ℝ)^i*((q : ℝ)^D*(2 : ℝ)^D*(N : ℝ)^(j-i)))*‖(v j : UnitAddCircle)‖ := by
            simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hwN (norm_nonneg (v j : UnitAddCircle))
          _ = (q : ℝ)^D*(2 : ℝ)^D*((N : ℝ)^j*‖(v j : UnitAddCircle)‖) := by
            rw [← hpw]
            ring
          _ ≤ (q : ℝ)^D*(2 : ℝ)^D*(A/ρ^D) :=
            mul_le_mul_of_nonneg_left hs' (by positivity)
          _ = _ := by ring
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end Hindman168
