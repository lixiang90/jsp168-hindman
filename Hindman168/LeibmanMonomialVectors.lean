import Hindman168.LeibmanPolynomialZeroCount
import Mathlib.LinearAlgebra.StdBasis

namespace Hindman168
open MvPolynomial
open scoped BigOperators Classical

noncomputable def leibmanMonomialVector {K : Type*} [CommSemiring K] {n : ℕ}
    (I : Finset (Fin n → ℕ)) (x : Fin n → K) : ↥I → K :=
  fun i => ∏ j, x j^(i.val j)

noncomputable def leibmanMonomialPolynomial {K : Type*} [CommSemiring K] {n : ℕ}
    (I : Finset (Fin n → ℕ)) (c : ↥I → K) : MvPolynomial (Fin n) K :=
  ∑ i : ↥I, monomial (Finsupp.equivFunOnFinite.symm i.val) (c i)

theorem leibman_monomial_polynomial_coeff {K : Type*} [CommSemiring K] {n : ℕ}
    (I : Finset (Fin n → ℕ)) (c : ↥I → K) (i : ↥I) :
    coeff (Finsupp.equivFunOnFinite.symm i.val) (leibmanMonomialPolynomial I c) = c i := by
  rw [leibmanMonomialPolynomial, coeff_sum]
  have he (j : ↥I) : Finsupp.equivFunOnFinite.symm j.val =
      Finsupp.equivFunOnFinite.symm i.val ↔ j = i := by
    constructor
    · intro h
      exact Subtype.ext (Finsupp.equivFunOnFinite.symm.injective h)
    · intro h
      exact congrArg (fun k : ↥I => Finsupp.equivFunOnFinite.symm k.val) h
  simp only [coeff_monomial, he, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem leibman_monomial_polynomial_eval {K : Type*} [CommSemiring K] {n : ℕ}
    (I : Finset (Fin n → ℕ)) (c : ↥I → K) (x : Fin n → K) :
    eval x (leibmanMonomialPolynomial I c) = ∑ i : ↥I, c i*leibmanMonomialVector I x i := by
  rw [leibmanMonomialPolynomial, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rfl

theorem leibman_monomial_polynomial_totalDegree {K : Type*} [CommSemiring K] {n : ℕ}
    (I : Finset (Fin n → ℕ)) (c : ↥I → K) (d : ℕ)
    (hd : ∀ i ∈ I, (∑ j, i j) ≤ d) : (leibmanMonomialPolynomial I c).totalDegree ≤ d := by
  apply totalDegree_finsetSum_le
  intro i _
  apply (totalDegree_monomial_le _ _).trans
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  exact hd i.val i.property

theorem leibman_monomial_polynomial_ne_zero {K : Type*} [CommSemiring K] {n : ℕ}
    (I : Finset (Fin n → ℕ)) (c : ↥I → K) (hc : c ≠ 0) :
    leibmanMonomialPolynomial I c ≠ 0 := by
  intro hz
  apply hc
  funext i
  have h := congrArg (coeff (Finsupp.equivFunOnFinite.symm i.val)) hz
  simpa only [leibman_monomial_polynomial_coeff, coeff_zero, Pi.zero_apply] using h

theorem leibman_monomial_vector_functional {K : Type*} [Field K] {n : ℕ}
    (I : Finset (Fin n → ℕ)) (f : (↥I → K) →ₗ[K] K) (x : Fin n → K) :
    eval x (leibmanMonomialPolynomial I (fun i => f (Pi.single i 1))) = f (leibmanMonomialVector I x) := by
  rw [leibman_monomial_polynomial_eval]
  have h : leibmanMonomialVector I x = ∑ i : ↥I,
      (leibmanMonomialVector I x i) • Pi.single i (1 : K) := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  conv_rhs => rw [h, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, smul_eq_mul, mul_comm]

theorem leibman_monomial_functional_coefficients_ne_zero {K : Type*} [Field K] {n : ℕ}
    (I : Finset (Fin n → ℕ)) (f : (↥I → K) →ₗ[K] K) (hf : f ≠ 0) :
    (fun i => f (Pi.single i 1)) ≠ 0 := by
  intro hz
  apply hf
  apply (Pi.basisFun K ↥I).ext
  intro i
  have h := congrFun hz i
  simpa only [Pi.basisFun_apply, LinearMap.zero_apply, Pi.zero_apply] using h

end Hindman168
