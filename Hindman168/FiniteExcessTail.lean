import Hindman168.SmallPrimeCommonDivisors
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Quantitative finite excess-product tails

Nonnegative local means multiply to a product bounded by the exponential
of their sum. When that sum is at most one the excess is at most twice
the sum. In particular the finite reciprocal-square majorant above w
has excess at most 2C/w, uniformly over the finite set of primes (or
indeed any finite set of integers above w).
-/

namespace Hindman168

open scoped BigOperators Classical

theorem finite_one_add_product_le_exp {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ S, 0 ≤ x i) :
    (∏ i ∈ S, (1 + x i)) - 1 ≤ Real.exp (∑ i ∈ S, x i) - 1 := by
  have h : (∏ i ∈ S, (1 + x i)) ≤ ∏ i ∈ S, Real.exp (x i) :=
    Finset.prod_le_prod (fun i hi => by linarith [hx i hi])
      (fun i _ => by simpa only [add_comm] using Real.add_one_le_exp (x i))
  rw [← Real.exp_sum] at h
  linarith

theorem finite_one_add_product_excess_le_twice_sum {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ S, 0 ≤ x i) (hs : (∑ i ∈ S, x i) ≤ 1) :
    0 ≤ (∏ i ∈ S, (1 + x i)) - 1 ∧
      (∏ i ∈ S, (1 + x i)) - 1 ≤ 2 * ∑ i ∈ S, x i := by
  have h0 : 0 ≤ ∑ i ∈ S, x i := Finset.sum_nonneg hx
  have hp : 1 ≤ ∏ i ∈ S, (1 + x i) := Finset.one_le_prod (fun i hi => by linarith [hx i hi])
  have he := Real.abs_exp_sub_one_le (show |∑ i ∈ S, x i| ≤ 1 from by rw [abs_of_nonneg h0]; exact hs)
  rw [abs_of_nonneg h0] at he
  have he' := (le_abs_self (Real.exp (∑ i ∈ S, x i) - 1)).trans he
  exact ⟨by linarith, (finite_one_add_product_le_exp S x hx).trans he'⟩

theorem reciprocal_square_product_excess_le {w : ℕ} (hw : 0 < w) (S : Finset ℕ)
    (hS : ∀ p ∈ S, w < p) (C : ℝ) (hC : 0 ≤ C) (hsmall : C ≤ (w : ℝ)) :
    0 ≤ (∏ p ∈ S, (1 + C * ((p : ℝ) ^ 2)⁻¹)) - 1 ∧
      (∏ p ∈ S, (1 + C * ((p : ℝ) ^ 2)⁻¹)) - 1 ≤ 2 * C / (w : ℝ) := by
  have hsum : (∑ p ∈ S, C * ((p : ℝ) ^ 2)⁻¹) ≤ C / (w : ℝ) := by
    rw [← Finset.mul_sum]
    simpa only [div_eq_mul_inv, one_div, one_mul] using
      mul_le_mul_of_nonneg_left (reciprocal_square_finset_tail_le hw S hS) hC
  have hone : C / (w : ℝ) ≤ 1 := (div_le_one (by exact_mod_cast hw : (0 : ℝ) < w)).mpr hsmall
  have h := finite_one_add_product_excess_le_twice_sum S
    (fun p => C * ((p : ℝ) ^ 2)⁻¹) (fun _ _ => by positivity) (hsum.trans hone)
  exact ⟨h.1, h.2.trans (by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 2))⟩

theorem bounded_local_means_product_excess_le {w : ℕ} (hw : 0 < w) (S : Finset ℕ)
    (hS : ∀ p ∈ S, w < p) (m : ℕ → ℝ) (hm : ∀ p ∈ S, 0 ≤ m p)
    (C : ℝ) (hC : 0 ≤ C) (hsmall : C ≤ (w : ℝ))
    (hbound : ∀ p ∈ S, m p ≤ C * ((p : ℝ) ^ 2)⁻¹) :
    0 ≤ (∏ p ∈ S, (1 + m p)) - 1 ∧ (∏ p ∈ S, (1 + m p)) - 1 ≤ 2 * C / (w : ℝ) := by
  have h0 : 1 ≤ ∏ p ∈ S, (1 + m p) := Finset.one_le_prod (fun p hp => by linarith [hm p hp])
  have hprod : (∏ p ∈ S, (1 + m p)) ≤ ∏ p ∈ S, (1 + C * ((p : ℝ) ^ 2)⁻¹) :=
    Finset.prod_le_prod (fun p hp => by linarith [hm p hp]) (fun p hp => by linarith [hbound p hp])
  have ht := (reciprocal_square_product_excess_le hw S hS C hC hsmall).2
  exact ⟨by linarith, by linarith⟩

end Hindman168
