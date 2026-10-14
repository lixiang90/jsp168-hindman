import Hindman168.CubeBinomialCoefficient

/-! No cancellation in the explicit scalar face/Taylor expansion. Identifying
this expression with the actual horizontal cube polynomial is a separate step. -/
namespace Hindman168
open scoped BigOperators
open MvPolynomial

theorem cube_binomial_face_isolated_coefficient {d : ℕ} (k j : ℕ)
    (A B : Finset (Fin d)) :
    coeff (cubeIsolatedMonomial j A) (cubeBinomialFacePolynomial k B) =
      if A = B then coeff (cubeIsolatedMonomial j A) (cubeBinomialPolynomial d k) else 0 := by
  rw [cubeBinomialFacePolynomial, cube_polynomial_face_part_coefficient,
    cube_isolated_monomial_support]

theorem cube_binomial_lower_order_coefficient {d : ℕ} (k j : ℕ)
    (A : Finset (Fin d)) (hA : A.card ≤ j) (hk : k < j) :
    coeff (cubeIsolatedMonomial j A) (cubeBinomialPolynomial d k) = 0 := by
  apply coeff_eq_zero_of_totalDegree_lt
  change (cubeBinomialPolynomial d k).totalDegree <
    (cubeIsolatedMonomial j A).sum (fun _ n => n)
  rw [cube_isolated_monomial_degree j A hA]
  exact (cube_binomial_polynomial_degree d k).trans_lt hk

noncomputable def cubeTaylorFaceScalarPolynomial {d : ℕ} (N : ℕ)
    (c : ℕ → Finset (Fin d) → ℝ) : MvPolynomial (Option (Fin d)) ℝ :=
  ∑ k ∈ Finset.range N, ∑ B : Finset (Fin d), C (c k B) * cubeBinomialFacePolynomial k B

theorem cube_taylor_face_scalar_isolated_coefficient {d : ℕ} (N j : ℕ)
    (A : Finset (Fin d)) (c : ℕ → Finset (Fin d) → ℝ)
    (hA : A.card ≤ j) (hj : j < N)
    (hTail : ∀ k, j < k → k < N → ∀ B : Finset (Fin d), B.card ≤ k → c k B = 0) :
    coeff (cubeIsolatedMonomial j A) (cubeTaylorFaceScalarPolynomial N c) =
      c j A / ((j - A.card).factorial : ℝ) := by
  classical
  have hi (k : ℕ) :
      (∑ B : Finset (Fin d), coeff (cubeIsolatedMonomial j A)
        (C (c k B) * cubeBinomialFacePolynomial k B)) =
      c k A * coeff (cubeIsolatedMonomial j A) (cubeBinomialPolynomial d k) := by
    simp only [coeff_C_mul, cube_binomial_face_isolated_coefficient, mul_ite, mul_zero]
    simp
  simp only [cubeTaylorFaceScalarPolynomial, coeff_sum, hi]
  rw [Finset.sum_eq_single j]
  · rw [cube_binomial_isolated_coefficient j A hA, div_eq_mul_inv]
  · intro k hk hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [cube_binomial_lower_order_coefficient k j A hA hlt, mul_zero]
    · rw [hTail k hgt (Finset.mem_range.mp hk) A (hA.trans hgt.le), zero_mul]
  · exact fun hn => False.elim (hn (Finset.mem_range.mpr hj))

end Hindman168
