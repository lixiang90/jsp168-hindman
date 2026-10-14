import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic

/-!
# Uniform polynomial-geometric bounds for local excess moments

One fixed summable half-geometric sequence supplies a constant depending
only on the polynomial degree. For every p >= 2, the positive-valuation
series is bounded by C/p, and every finite rectangular two-valuation
sum by C_k C_l/p^2. The constants do not depend on p or the cutoffs.
-/

namespace Hindman168

open scoped BigOperators Classical

noncomputable def polynomialGeometricConstant (k : ℕ) : ℝ :=
  ∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ k * (1 / 2 : ℝ) ^ n

theorem polynomialHalfGeometric_summable (k : ℕ) :
    Summable (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ k * (1 / 2 : ℝ) ^ n) := by
  have h0 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) k
    (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
  have hs : Summable (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ k * (1 / 2 : ℝ) ^ (n + 2)) :=
    h0.comp_injective (fun a b h => Nat.add_right_cancel h)
  apply (hs.mul_left 4).congr
  intro n
  rw [pow_add]
  norm_num
  ring

theorem polynomialGeometricConstant_nonneg (k : ℕ) : 0 ≤ polynomialGeometricConstant k :=
  tsum_nonneg (fun _ => by positivity)

theorem polynomial_geometric_term_le_half (k p : ℕ) (hp : 2 ≤ p) (n : ℕ) :
    ((n + 2 : ℕ) : ℝ) ^ k * ((p : ℝ) ^ (n + 1))⁻¹ ≤
      (p : ℝ)⁻¹ * (((n + 2 : ℕ) : ℝ) ^ k * (1 / 2 : ℝ) ^ n) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hhalf : (p : ℝ)⁻¹ ≤ (1 / 2 : ℝ) := by
    rw [← one_div]
    apply (div_le_div_iff₀ hpR (by norm_num : (0 : ℝ) < 2)).mpr
    simpa only [one_mul] using (show (2 : ℝ) ≤ p from by exact_mod_cast hp)
  have hpow : (p : ℝ)⁻¹ ^ n ≤ (1 / 2 : ℝ) ^ n :=
    pow_le_pow_left₀ (by positivity) hhalf n
  have he : ((n + 2 : ℕ) : ℝ) ^ k * ((p : ℝ) ^ (n + 1))⁻¹ =
      (p : ℝ)⁻¹ * (((n + 2 : ℕ) : ℝ) ^ k * (p : ℝ)⁻¹ ^ n) := by
    rw [pow_succ, mul_inv_rev, inv_pow]
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)

theorem finite_polynomial_geometric_bound (k p : ℕ) (hp : 2 ≤ p) (S : Finset ℕ) :
    (∑ n ∈ S, ((n + 2 : ℕ) : ℝ) ^ k * ((p : ℝ) ^ (n + 1))⁻¹) ≤
      polynomialGeometricConstant k / (p : ℝ) := by
  calc
    _ ≤ ∑ n ∈ S, (p : ℝ)⁻¹ * (((n + 2 : ℕ) : ℝ) ^ k * (1 / 2 : ℝ) ^ n) :=
      Finset.sum_le_sum (fun n _ => polynomial_geometric_term_le_half k p hp n)
    _ = (p : ℝ)⁻¹ * ∑ n ∈ S, ((n + 2 : ℕ) : ℝ) ^ k * (1 / 2 : ℝ) ^ n :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (p : ℝ)⁻¹ * polynomialGeometricConstant k :=
      mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum S (fun _ _ => by positivity) (polynomialHalfGeometric_summable k)) (by positivity)
    _ = _ := by rw [div_eq_mul_inv]; ring

theorem polynomial_geometric_summable (k p : ℕ) (hp : 2 ≤ p) :
    Summable (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ k * ((p : ℝ) ^ (n + 1))⁻¹) := by
  exact ((polynomialHalfGeometric_summable k).mul_left (p : ℝ)⁻¹).of_nonneg_of_le
    (fun _ => by positivity) (polynomial_geometric_term_le_half k p hp)

theorem polynomial_geometric_tsum_bound (k p : ℕ) (hp : 2 ≤ p) :
    (∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ k * ((p : ℝ) ^ (n + 1))⁻¹) ≤
      polynomialGeometricConstant k / (p : ℝ) := by
  have h := Summable.tsum_le_tsum (polynomial_geometric_term_le_half k p hp)
    (polynomial_geometric_summable k p hp)
    ((polynomialHalfGeometric_summable k).mul_left (p : ℝ)⁻¹)
  rw [tsum_mul_left] at h
  simpa only [polynomialGeometricConstant, div_eq_mul_inv, mul_comm] using h

theorem finite_polynomial_geometric_pair_bound (k l p : ℕ) (hp : 2 ≤ p) (S T : Finset ℕ) :
    (∑ n ∈ S, ∑ m ∈ T, (((n + 2 : ℕ) : ℝ) ^ k * ((m + 2 : ℕ) : ℝ) ^ l) *
      ((p : ℝ) ^ (n + m + 2))⁻¹) ≤
      (polynomialGeometricConstant k * polynomialGeometricConstant l) / (p : ℝ) ^ 2 := by
  have he (n m : ℕ) : (((n + 2 : ℕ) : ℝ) ^ k * ((m + 2 : ℕ) : ℝ) ^ l) *
      ((p : ℝ) ^ (n + m + 2))⁻¹ =
      (((n + 2 : ℕ) : ℝ) ^ k * ((p : ℝ) ^ (n + 1))⁻¹) *
        (((m + 2 : ℕ) : ℝ) ^ l * ((p : ℝ) ^ (m + 1))⁻¹) := by
    have hn : n + m + 2 = (n + 1) + (m + 1) := by omega
    rw [hn, pow_add, mul_inv_rev]
    ring
  have hsum : (∑ n ∈ S, ∑ m ∈ T, (((n + 2 : ℕ) : ℝ) ^ k * ((m + 2 : ℕ) : ℝ) ^ l) *
      ((p : ℝ) ^ (n + m + 2))⁻¹) =
      (∑ n ∈ S, ((n + 2 : ℕ) : ℝ) ^ k * ((p : ℝ) ^ (n + 1))⁻¹) *
        (∑ m ∈ T, ((m + 2 : ℕ) : ℝ) ^ l * ((p : ℝ) ^ (m + 1))⁻¹) := by
    simp_rw [he]
    exact (Finset.sum_mul_sum _ _ _ _).symm
  rw [hsum]
  calc
    _ ≤ (polynomialGeometricConstant k / (p : ℝ)) * (polynomialGeometricConstant l / (p : ℝ)) :=
      mul_le_mul (finite_polynomial_geometric_bound k p hp S) (finite_polynomial_geometric_bound l p hp T)
        (Finset.sum_nonneg (fun _ _ => by positivity)) (div_nonneg (polynomialGeometricConstant_nonneg k) (Nat.cast_nonneg p))
    _ = _ := by rw [div_mul_div_comm, pow_two]

end Hindman168
