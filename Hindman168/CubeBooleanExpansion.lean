import Hindman168.CubeBinomialCoefficient

/-! Vertex restriction is exactly the Boolean sum of the included faces,
not an assumed polynomial expansion. -/
namespace Hindman168
open scoped BigOperators
open MvPolynomial

def cubeVertexVariables {d : ℕ} (V : Finset (Fin d))
    (b : Option (Fin d) → ℝ) (i : Option (Fin d)) : ℝ :=
  match i with
  | none => b none
  | some k => if k ∈ V then b (some k) else 0

theorem cube_vertex_monomial_eval {d : ℕ} (V : Finset (Fin d))
    (b : Option (Fin d) → ℝ) (m : Option (Fin d) →₀ ℕ) (c : ℝ) :
    eval (cubeVertexVariables V b) (monomial m c) =
      if cubeIncrementSupport m ⊆ V then eval b (monomial m c) else 0 := by
  classical
  simp only [eval_monomial]
  split_ifs with h
  · congr 1
    apply Finset.prod_congr rfl
    intro i hi
    cases i with
    | none => rfl
    | some k =>
      have hk : k ∈ V := h (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, Finsupp.mem_support_iff.mp hi⟩)
      simp [cubeVertexVariables, hk]
  · obtain ⟨k, hk, hv⟩ := Finset.not_subset.mp h
    have hm : m (some k) ≠ 0 := (Finset.mem_filter.mp hk).2
    have hz : m.prod (fun i n => cubeVertexVariables V b i ^ n) = 0 := by
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hm)
      simp [cubeVertexVariables, hv, zero_pow hm]
    rw [hz, mul_zero]

theorem cube_vertex_face_part_eval {d : ℕ} (V A : Finset (Fin d))
    (b : Option (Fin d) → ℝ) (p : MvPolynomial (Option (Fin d)) ℝ) :
    eval (cubeVertexVariables V b) (cubePolynomialFacePart A p) =
      if A ⊆ V then eval b (cubePolynomialFacePart A p) else 0 := by
  classical
  have he := (cubePolynomialFacePart A p).as_sum
  rw [he]
  simp only [eval_sum]
  split_ifs with h
  · apply Finset.sum_congr rfl
    intro m hm
    rw [cube_polynomial_face_part_support] at hm
    have hs : cubeIncrementSupport m = A := (Finset.mem_filter.mp hm).2
    rw [cube_vertex_monomial_eval, hs, if_pos h]
  · apply Finset.sum_eq_zero
    intro m hm
    rw [cube_polynomial_face_part_support] at hm
    have hs : cubeIncrementSupport m = A := (Finset.mem_filter.mp hm).2
    rw [cube_vertex_monomial_eval, hs, if_neg h]

theorem cube_boolean_polynomial_expansion {d : ℕ} (V : Finset (Fin d))
    (b : Option (Fin d) → ℝ) (p : MvPolynomial (Option (Fin d)) ℝ) :
    eval (cubeVertexVariables V b) p =
      ∑ A : Finset (Fin d), if A ⊆ V then eval b (cubePolynomialFacePart A p) else 0 := by
  conv_lhs => rw [← cube_polynomial_face_parts_sum p]
  simp only [eval_sum, cube_vertex_face_part_eval]

theorem cube_boolean_binomial_expansion {d : ℕ} (j : ℕ) (V : Finset (Fin d))
    (b : Option (Fin d) → ℝ) :
    (scalarBinomialPolynomial j).eval (b none + ∑ k ∈ V, b (some k)) =
      ∑ A : Finset (Fin d), if A ⊆ V then eval b (cubeBinomialFacePolynomial j A) else 0 := by
  have he := cube_boolean_polynomial_expansion V b (cubeBinomialPolynomial d j)
  change _ = ∑ A : Finset (Fin d), if A ⊆ V then
    eval b (cubePolynomialFacePart A (cubeBinomialPolynomial d j)) else 0
  rw [← he, cubeBinomialPolynomial]
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def, eval_sum]
  simp only [map_mul, eval_C, map_pow, eval_sum, eval_X]
  rw [Fintype.sum_option]
  simp only [cubeVertexVariables, Finset.sum_ite_mem, Finset.univ_inter]
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]

end Hindman168
