import Hindman168.IntegerWeightedModOneNorm
import Hindman168.ScalarPolynomialTopRemoval
import Hindman168.ModOneNaturalMultiplier

namespace Hindman168
open Polynomial
open scoped BigOperators Classical

/-- Recover the ACTUAL constant from one ACTUAL small-value sample and the
same multiplier's controlled nonconstant coefficients. No coarse constant
estimate is assumed. -/
theorem polynomial_small_value_constant_recovery (p : ℝ[X]) (D n N q : ℕ)
    (hp : p.natDegree ≤ D) (hn : n ≤ N) (ε C : ℝ)
    (hsmall : ‖((p.eval (n : ℝ) : ℝ) : UnitAddCircle)‖ ≤ ε)
    (hcoeff : ∀ i : ℕ, 0 < i → i ≤ D →
      (N : ℝ)^i*‖(((q : ℝ)*p.coeff i : ℝ) : UnitAddCircle)‖ ≤ C*ε) :
    ‖(((q : ℝ)*p.coeff 0 : ℝ) : UnitAddCircle)‖ ≤ (q : ℝ)*ε+(D : ℝ)*C*ε := by
  have heval : p.eval (n : ℝ) = (∑ j ∈ Finset.range D, p.coeff (j+1)*(n : ℝ)^(j+1))+p.coeff 0 := by
    rw [eval_eq_sum_range' (by omega : p.natDegree < D+1), Finset.sum_range_succ']
    simp only [pow_zero, mul_one]
  let b := round ((q : ℝ)*p.eval (n : ℝ))
  let c := fun j => round ((q : ℝ)*p.coeff (j+1))
  apply (rough_mod_one_near_integer_iff _ _).mpr
  refine ⟨b-∑ j ∈ Finset.range D, (n : ℤ)^(j+1)*c j, ?_⟩
  have he : (q : ℝ)*p.coeff 0-((b-∑ j ∈ Finset.range D, (n : ℤ)^(j+1)*c j : ℤ) : ℝ) =
      ((q : ℝ)*p.eval (n : ℝ)-(b : ℝ))-
        ∑ j ∈ Finset.range D, (n : ℝ)^(j+1)*((q : ℝ)*p.coeff (j+1)-(c j : ℝ)) := by
    have hs : (∑ j ∈ Finset.range D, (n : ℝ)^(j+1)*((q : ℝ)*p.coeff (j+1)-(c j : ℝ))) =
        (∑ j ∈ Finset.range D, (q : ℝ)*(p.coeff (j+1)*(n : ℝ)^(j+1)))-
          ∑ j ∈ Finset.range D, (n : ℝ)^(j+1)*(c j : ℝ) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [heval]
    push_cast
    rw [hs, mul_add, Finset.mul_sum]
    ring
  rw [he]
  have hsample : |(q : ℝ)*p.eval (n : ℝ)-(b : ℝ)| ≤ (q : ℝ)*ε := by
    rw [← UnitAddCircle.norm_eq]
    exact (mod_one_natural_multiplier_norm_le q _).trans
      (mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg q))
  have hsum : (∑ j ∈ Finset.range D,
      |(n : ℝ)^(j+1)*((q : ℝ)*p.coeff (j+1)-(c j : ℝ))|) ≤ (D : ℝ)*C*ε := by
    calc
      _ ≤ ∑ _j ∈ Finset.range D, C*ε := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg n) _)]
        change (n : ℝ)^(j+1)*|(q : ℝ)*p.coeff (j+1)-round ((q : ℝ)*p.coeff (j+1))| ≤ _
        rw [← UnitAddCircle.norm_eq]
        have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn
        exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg n) hnN _)
          (norm_nonneg _)).trans (hcoeff (j+1) (by omega) (Finset.mem_range.mp hj))
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  exact (abs_sub _ _).trans (by
    have hs := Finset.abs_sum_le_sum_abs (fun j => (n : ℝ)^(j+1)*
      ((q : ℝ)*p.coeff (j+1)-(c j : ℝ))) (Finset.range D)
    linarith)

end Hindman168
