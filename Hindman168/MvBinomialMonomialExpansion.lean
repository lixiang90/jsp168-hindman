import Hindman168.MvBinomialCoefficients
import Hindman168.ScalarRoughBinomialCompatibility
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Hindman168
open MvPolynomial
open scoped BigOperators Classical

theorem mv_coordinate_stirling_expansion {κ : Type*} (j : κ) (r D : ℕ) (hr : r ≤ D) :
    (X j : MvPolynomial κ ℝ)^r = ∑ i ∈ Finset.range (D+1),
      C (Nat.stirlingSecond r i : ℝ)*∏ t ∈ Finset.range i, (X j-C (t : ℝ)) := by
  have h := congrArg (Polynomial.eval₂RingHom C (X j))
    (scalar_polynomial_stirling_expansion_bounded r D hr)
  simp only [map_pow, map_sum, map_mul, scalar_desc_pochhammer_product, map_prod, map_sub] at h
  simpa only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, Polynomial.eval₂_C] using h

/-- Exact factorial cancellation identifies the actual tensor falling
factorial expansion with the ORIGINAL rough-box binomial basis. -/
theorem mv_binomial_stirling_basis_term {κ : Type*} [Fintype κ] (I J : κ → ℕ) :
    (∏ j, C (Nat.stirlingSecond (J j) (I j) : ℝ)*
      ∏ t ∈ Finset.range (I j), (X j-C (t : ℝ))) =
      C (mvBinomialStirlingWeight I J : ℝ)*roughMvBinomialPolynomial I := by
  rw [mvBinomialStirlingWeight, Nat.cast_prod, map_prod, roughMvBinomialPolynomial,
    roughMvFallingPolynomial, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  have hc : ((I j).factorial : ℝ) ≠ 0 := by positivity
  have he : C (((I j).factorial*Nat.stirlingSecond (J j) (I j) : ℕ) : ℝ)*
    C (((I j).factorial : ℝ)⁻¹) = (C (Nat.stirlingSecond (J j) (I j) : ℝ) : MvPolynomial κ ℝ) := by
    rw [← map_mul]
    congr 1
    push_cast
    field_simp
  rw [← mul_assoc, he]

/-- Actual ordinary multivariate monomial expanded in the actual binomial
basis, with NATURAL INTEGER tensor Stirling weights and a fixed exponent box. -/
theorem mv_monomial_binomial_expansion {κ : Type*} [Fintype κ]
    (J : κ → ℕ) (D : ℕ) (hJ : ∀ j, J j ≤ D) :
    (∏ j, (X j : MvPolynomial κ ℝ)^(J j)) =
      ∑ I ∈ mvBinomialBox κ D, C (mvBinomialStirlingWeight I J : ℝ)*roughMvBinomialPolynomial I := by
  simp_rw [mv_coordinate_stirling_expansion _ _ D (hJ _)]
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro I _
  exact mv_binomial_stirling_basis_term I J

end Hindman168
