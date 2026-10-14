import Hindman168.CubePolynomialFacePart
import Hindman168.NativeSubgroupTaylorTopCoefficient
import Mathlib.Algebra.MvPolynomial.Coeff

/-! Coefficients of the actual binomial polynomial in the base and increment
variables. The selected monomial has each chosen increment exactly once. -/
namespace Hindman168
open scoped BigOperators
open MvPolynomial

theorem cube_polynomial_sum_coefficient (d : ℕ) (P : Polynomial ℝ)
    (m : Option (Fin d) →₀ ℕ) :
    coeff m (P.eval₂ C (∑ i : Option (Fin d), X i)) =
      P.coeff (m.sum (fun _ n => n)) * (m.multinomial : ℝ) := by
  classical
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def, coeff_sum]
  simp only [coeff_C_mul, coeff_sum_X_pow_of_fintype]
  rw [Finset.sum_eq_single (m.sum (fun _ n => n))]
  · simp
  · intro b hb hne
    simp [Ne.symm hne]
  · intro hn
    simp [Polynomial.notMem_support_iff.mp hn]

noncomputable def cubeBinomialPolynomial (d j : ℕ) :
    MvPolynomial (Option (Fin d)) ℝ :=
  (scalarBinomialPolynomial j).eval₂ C (∑ i : Option (Fin d), X i)

noncomputable def cubeBinomialFacePolynomial {d : ℕ} (j : ℕ) (A : Finset (Fin d)) :
    MvPolynomial (Option (Fin d)) ℝ :=
  cubePolynomialFacePart A (cubeBinomialPolynomial d j)

theorem cube_binomial_polynomial_degree (d j : ℕ) :
    (cubeBinomialPolynomial d j).totalDegree ≤ j := by
  apply Finset.sup_le
  intro m hm
  have hn := mem_support_iff.mp hm
  rw [cubeBinomialPolynomial, cube_polynomial_sum_coefficient] at hn
  exact (Polynomial.le_natDegree_of_ne_zero (mul_ne_zero_iff.mp hn).1).trans
    (scalar_binomial_polynomial_degree_le j)

theorem cube_binomial_face_degree {d : ℕ} (j : ℕ) (A : Finset (Fin d)) :
    (cubeBinomialFacePolynomial j A).totalDegree ≤ j :=
  (cube_polynomial_face_part_degree A _).trans (cube_binomial_polynomial_degree d j)

theorem cube_binomial_face_eq_zero {d : ℕ} (j : ℕ) (A : Finset (Fin d))
    (h : j < A.card) : cubeBinomialFacePolynomial j A = 0 :=
  cube_polynomial_face_part_eq_zero_of_degree A _
    ((cube_binomial_polynomial_degree d j).trans_lt h)

noncomputable def cubeIsolatedMonomial {d : ℕ} (j : ℕ) (A : Finset (Fin d)) :
    Option (Fin d) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => match i with
    | none => j - A.card
    | some k => if k ∈ A then 1 else 0)

theorem cube_isolated_monomial_support {d : ℕ} (j : ℕ) (A : Finset (Fin d)) :
    cubeIncrementSupport (cubeIsolatedMonomial j A) = A := by
  ext k
  simp [cubeIncrementSupport, cubeIsolatedMonomial]

theorem cube_isolated_monomial_degree {d : ℕ} (j : ℕ) (A : Finset (Fin d))
    (h : A.card ≤ j) : (cubeIsolatedMonomial j A).sum (fun _ n => n) = j := by
  rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_option]
  simp [cubeIsolatedMonomial, Nat.sub_add_cancel h]

theorem cube_isolated_monomial_factorial {d : ℕ} (j : ℕ) (A : Finset (Fin d))
    (h : A.card ≤ j) :
    (j - A.card).factorial * (cubeIsolatedMonomial j A).multinomial = j.factorial := by
  have he := Nat.multinomial_spec Finset.univ (cubeIsolatedMonomial j A)
  rw [← Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)] at he
  have hs : (∑ i : Option (Fin d), cubeIsolatedMonomial j A i) = j := by
    have ht := cube_isolated_monomial_degree j A h
    rw [Finsupp.sum_fintype _ _ (by simp)] at ht
    exact ht
  rw [hs] at he
  simpa [Fintype.prod_option, cubeIsolatedMonomial, apply_ite Nat.factorial] using he

theorem cube_binomial_isolated_coefficient {d : ℕ} (j : ℕ) (A : Finset (Fin d))
    (h : A.card ≤ j) :
    coeff (cubeIsolatedMonomial j A) (cubeBinomialPolynomial d j) =
      ((j - A.card).factorial : ℝ)⁻¹ := by
  rw [cubeBinomialPolynomial, cube_polynomial_sum_coefficient,
    cube_isolated_monomial_degree j A h, scalar_binomial_polynomial_top_coefficient]
  have he : ((j - A.card).factorial : ℝ) *
      ((cubeIsolatedMonomial j A).multinomial : ℝ) = (j.factorial : ℝ) := by
    exact_mod_cast cube_isolated_monomial_factorial j A h
  have hj : (j.factorial : ℝ) ≠ 0 := by positivity
  have ha : ((j - A.card).factorial : ℝ) ≠ 0 := by positivity
  apply (mul_left_cancel₀ ha)
  calc
    _ = (j.factorial : ℝ)⁻¹ * (((j - A.card).factorial : ℝ) *
        ((cubeIsolatedMonomial j A).multinomial : ℝ)) := by ring
    _ = 1 := by rw [he, inv_mul_cancel₀ hj]
    _ = _ := (mul_inv_cancel₀ ha).symm

end Hindman168
