import Hindman168.FiniteVectorPolynomialRational

/-! Actual finite sums and iterated bilinear powers of polynomial lists,
with true evaluation and rational coefficient membership laws. -/

namespace Hindman168
open Finset

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def finiteVectorPolynomialSum (n : ℕ) (P : ℕ → List (ℕ × E)) : List (ℕ × E) :=
  ((List.range n).map P).flatten

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
 theorem finiteVectorPolynomialSum_succ (n : ℕ) (P : ℕ → List (ℕ × E)) :
    finiteVectorPolynomialSum (n + 1) P = finiteVectorPolynomialSum n P ++ P n := by
  simp only [finiteVectorPolynomialSum, List.range_succ, List.map_append,
    List.flatten_append, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, List.append_nil]

 theorem finiteVectorPolynomialEval_sum (n : ℕ) (P : ℕ → List (ℕ × E)) (t : ℝ) :
    finiteVectorPolynomialEval (finiteVectorPolynomialSum n P) t =
      ∑ j ∈ range n, finiteVectorPolynomialEval (P j) t := by
  induction n with
  | zero => simp only [finiteVectorPolynomialSum, List.range_zero, List.map_nil,
      List.flatten_nil, finiteVectorPolynomialEval_nil, Finset.range_zero, sum_empty]
  | succ n ih =>
    rw [finiteVectorPolynomialSum_succ, finiteVectorPolynomialEval_append, ih, sum_range_succ]

noncomputable def finiteVectorPolynomialAdPower
    (B : E →L[ℝ] (E →L[ℝ] E)) (p q : List (ℕ × E)) : ℕ → List (ℕ × E)
  | 0 => q
  | n + 1 => finiteVectorPolynomialBilinear B p (finiteVectorPolynomialAdPower B p q n)

 theorem finiteVectorPolynomialEval_adPower
    (B : E →L[ℝ] (E →L[ℝ] E)) (p q : List (ℕ × E)) (n : ℕ) (t : ℝ) :
    finiteVectorPolynomialEval (finiteVectorPolynomialAdPower B p q n) t =
      ((B (finiteVectorPolynomialEval p t)) ^ n) (finiteVectorPolynomialEval q t) := by
  induction n with
  | zero => simp only [finiteVectorPolynomialAdPower, pow_zero, one_apply_eq_self]
  | succ n ih =>
    rw [finiteVectorPolynomialAdPower, finiteVectorPolynomialEval_bilinear, ih, pow_succ']
    rfl

variable [Module ℚ E]

omit [NormedSpace ℝ E] in
 theorem finiteVectorPolynomialCoefficientsMem_sum (V : Submodule ℚ E)
    (n : ℕ) (P : ℕ → List (ℕ × E))
    (h : ∀ j < n, finiteVectorPolynomialCoefficientsMem V (P j)) :
    finiteVectorPolynomialCoefficientsMem V (finiteVectorPolynomialSum n P) := by
  apply finiteVectorPolynomialCoefficientsMem_flatten
  intro p hp
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
  exact h j (List.mem_range.mp hj)

 theorem finiteVectorPolynomialCoefficientsMem_adPower (V : Submodule ℚ E)
    (B : E →L[ℝ] (E →L[ℝ] E))
    (hB : ∀ v ∈ V, ∀ w ∈ V, B v w ∈ V)
    {p q : List (ℕ × E)} (hp : finiteVectorPolynomialCoefficientsMem V p)
    (hq : finiteVectorPolynomialCoefficientsMem V q) (n : ℕ) :
    finiteVectorPolynomialCoefficientsMem V (finiteVectorPolynomialAdPower B p q n) := by
  induction n with
  | zero => exact hq
  | succ n ih => exact finiteVectorPolynomialCoefficientsMem_bilinear V B hB hp ih

end Hindman168
