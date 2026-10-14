import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Data.Real.Basic

/-! A finite real vector polynomial is determined by its values at all
natural numbers. Actual algebraic duals reduce the claim to scalar
polynomial uniqueness on the genuine infinite natural-number set. -/

namespace Hindman168
open Finset Polynomial Set Function

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

 theorem vectorPolynomial_coeff_eq_of_nat_values {k : ℕ} {a b : ℕ → V}
    (h : ∀ n : ℕ, (∑ j ∈ range k, ((n : ℝ) ^ j) • a j) =
      ∑ j ∈ range k, ((n : ℝ) ^ j) • b j) {j : ℕ} (hj : j < k) : a j = b j := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℝ (a j - b j)).mp
  intro φ
  let p : Polynomial ℝ := ∑ i ∈ range k, monomial i (φ (a i))
  let q : Polynomial ℝ := ∑ i ∈ range k, monomial i (φ (b i))
  have he : ∀ n : ℕ, p.eval (n : ℝ) = q.eval (n : ℝ) := by
    intro n
    have hm := congrArg φ (h n)
    simpa only [p, q, eval_finsetSum, eval_monomial, map_sum, map_smul,
      smul_eq_mul, mul_comm] using hm
  have hi : Set.Infinite {t : ℝ | p.eval t = q.eval t} := by
    apply (Set.infinite_range_of_injective (Nat.cast_injective :
      Injective (fun n : ℕ => (n : ℝ)))).mono
    rintro t ⟨n, rfl⟩
    exact he n
  have hpq : p = q := Polynomial.eq_of_infinite_eval_eq p q hi
  have hc := congrArg (fun r : Polynomial ℝ => r.coeff j) hpq
  have hc' : φ (a j) = φ (b j) := by
    simpa only [p, q, finsetSum_coeff, coeff_monomial, sum_ite_eq', Finset.mem_range, hj,
      if_true] using hc
  rw [map_sub, hc', sub_self]

end Hindman168
