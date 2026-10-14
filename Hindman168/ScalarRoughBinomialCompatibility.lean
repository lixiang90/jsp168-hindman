import Hindman168.ScalarPolynomialBinomialExpansion
import Hindman168.RoughBinomialDenominator
import Mathlib.Algebra.MvPolynomial.Equiv

namespace Hindman168
open Polynomial
open scoped BigOperators

theorem scalar_desc_pochhammer_product (i : ℕ) :
    descPochhammer ℝ i = ∏ k ∈ Finset.range i,
      ((Polynomial.X : ℝ[X])-Polynomial.C (k : ℝ)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [descPochhammer_succ_right, ih, Finset.prod_range_succ]
    simp only [Polynomial.C_eq_natCast]

/-- Actual agreement with the rough-box binomial basis in one variable. -/
theorem scalar_rough_binomial_compatibility {κ : Type*} [Fintype κ] [Unique κ]
    (i : ℕ) :
    MvPolynomial.uniqueAlgEquiv ℝ κ (roughMvBinomialPolynomial (fun _ : κ => i)) =
      scalarBinomialPolynomial i := by
  simp only [roughMvBinomialPolynomial, roughMvFallingPolynomial,
    MvPolynomial.uniqueAlgEquiv_apply, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_prod,
    MvPolynomial.eval₂_C, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_X,
    Fintype.prod_unique, scalarBinomialPolynomial, scalar_desc_pochhammer_product]

theorem scalar_rough_binomial_expansion {κ : Type*} [Fintype κ] [Unique κ]
    (p : ℝ[X]) (D : ℕ) (hp : p.natDegree ≤ D) :
    (MvPolynomial.uniqueAlgEquiv ℝ κ).symm p =
      ∑ i ∈ Finset.range (D+1),
        MvPolynomial.C (scalarPolynomialBinomialCoefficient p D i)*
          roughMvBinomialPolynomial (fun _ : κ => i) := by
  apply (MvPolynomial.uniqueAlgEquiv ℝ κ).injective
  simp only [AlgEquiv.apply_symm_apply, map_sum, map_mul,
    MvPolynomial.uniqueAlgEquiv_apply, MvPolynomial.eval₂_C]
  simp_rw [← MvPolynomial.uniqueAlgEquiv_apply, scalar_rough_binomial_compatibility]
  exact scalar_polynomial_binomial_expansion p D hp

end Hindman168
