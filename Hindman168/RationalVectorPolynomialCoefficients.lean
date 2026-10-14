import Hindman168.VectorPolynomialNatUniqueness
import Mathlib.Algebra.Module.Rat
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.Analysis.Normed.Module.Basic

/-! Finite vector polynomials with rational scalars can have their
coefficients recovered algebraically from natural-number values. Applying
this in the actual Q-linear quotient proves rational coefficient membership
without any topological closure assumption on the rational subspace. -/

namespace Hindman168
open Finset Polynomial Set Function

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

 theorem rationalVectorPolynomial_coeff_eq_of_nat_values {k : ℕ} {a b : ℕ → V}
    (h : ∀ n : ℕ, (∑ j ∈ range k, ((n : ℚ) ^ j) • a j) =
      ∑ j ∈ range k, ((n : ℚ) ^ j) • b j) {j : ℕ} (hj : j < k) : a j = b j := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℚ (a j - b j)).mp
  intro φ
  let p : Polynomial ℚ := ∑ i ∈ range k, monomial i (φ (a i))
  let q : Polynomial ℚ := ∑ i ∈ range k, monomial i (φ (b i))
  have he : ∀ n : ℕ, p.eval (n : ℚ) = q.eval (n : ℚ) := by
    intro n
    have hm := congrArg φ (h n)
    simpa only [p, q, eval_finsetSum, eval_monomial, map_sum, map_smul,
      smul_eq_mul, mul_comm] using hm
  have hi : Set.Infinite {t : ℚ | p.eval t = q.eval t} := by
    apply (Set.infinite_range_of_injective (Nat.cast_injective :
      Injective (fun n : ℕ => (n : ℚ)))).mono
    rintro t ⟨n, rfl⟩
    exact he n
  have hpq : p = q := Polynomial.eq_of_infinite_eval_eq p q hi
  have hc := congrArg (fun r : Polynomial ℚ => r.coeff j) hpq
  have hc' : φ (a j) = φ (b j) := by
    simpa only [p, q, finsetSum_coeff, coeff_monomial, sum_ite_eq', Finset.mem_range, hj,
      if_true] using hc
  rw [map_sub, hc', sub_self]

 theorem rationalVectorPolynomial_coeff_mem_of_nat_values
    (S : Submodule ℚ V) {k : ℕ} {a : ℕ → V}
    (h : ∀ n : ℕ, (∑ i ∈ range k, ((n : ℚ) ^ i) • a i) ∈ S)
    {j : ℕ} (hj : j < k) : a j ∈ S := by
  have hz : ∀ n : ℕ, (∑ i ∈ range k, ((n : ℚ) ^ i) • S.mkQ (a i)) =
      ∑ i ∈ range k, ((n : ℚ) ^ i) • (0 : V ⧸ S) := by
    intro n
    calc
      _ = S.mkQ (∑ i ∈ range k, ((n : ℚ) ^ i) • a i) := by
        simp only [map_sum, map_smul]
      _ = 0 := (Submodule.Quotient.mk_eq_zero S).mpr (h n)
      _ = _ := by simp only [smul_zero, sum_const_zero]
  have hc : S.mkQ (a j) = 0 := rationalVectorPolynomial_coeff_eq_of_nat_values hz hj
  exact (Submodule.Quotient.mk_eq_zero S).mp hc

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module ℚ E]

 theorem rationalVectorPolynomial_coeff_mem_of_real_nat_values
    (S : Submodule ℚ E) {k : ℕ} {a : ℕ → E}
    (h : ∀ n : ℕ, (∑ i ∈ range k, ((n : ℝ) ^ i) • a i) ∈ S)
    {j : ℕ} (hj : j < k) : a j ∈ S := by
  apply rationalVectorPolynomial_coeff_mem_of_nat_values S _ hj
  intro n
  have he : (∑ i ∈ range k, ((n : ℚ) ^ i) • a i) =
      ∑ i ∈ range k, ((n : ℝ) ^ i) • a i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Rat.cast_smul_eq_qsmul ℝ]
    push_cast
    rfl
  rw [he]
  exact h n

end Hindman168
