import Hindman168.NativeLieRationalDefectPolynomial

/-! Finite rational polynomial representations for all genuine defect
powers and the actual logarithm-lifting vector field. The real evaluation
equals the original finite inverse differential, not a supplied model. -/

namespace Hindman168
open Finset
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeLieRationalDefectPowerPolynomial (p q : List (ℕ × E)) : ℕ → List (ℕ × E)
  | 0 => q
  | n + 1 => nativeLieRationalDefectPolynomial (I := I) (G := G) p
      (nativeLieRationalDefectPowerPolynomial p q n)

 theorem nativeLieRationalDefectPowerPolynomial_eval (p q : List (ℕ × E)) (n : ℕ) (t : ℝ) :
    finiteVectorPolynomialEval (nativeLieRationalDefectPowerPolynomial (I := I) (G := G) p q n) t =
      (nativeLieDexpDefect (I := I) (G := G) (finiteVectorPolynomialEval p t) ^ n)
        (finiteVectorPolynomialEval q t) := by
  induction n with
  | zero => simp only [nativeLieRationalDefectPowerPolynomial, pow_zero, one_apply_eq_self]
  | succ n ih =>
    rw [nativeLieRationalDefectPowerPolynomial, nativeLieRationalDefectPolynomial_eval, ih, pow_succ']
    rfl

noncomputable def nativeLieRationalFieldPolynomial (p q : List (ℕ × E)) : List (ℕ × E) :=
  finiteVectorPolynomialSum (Group.nilpotencyClass G)
    (nativeLieRationalDefectPowerPolynomial (I := I) (G := G) p q)

 theorem nativeLieRationalFieldPolynomial_eval (p q : List (ℕ × E)) (t : ℝ) :
    finiteVectorPolynomialEval (nativeLieRationalFieldPolynomial (I := I) (G := G) p q) t =
      nativeLieLogarithmVectorField (I := I) (G := G) (finiteVectorPolynomialEval q t)
        (finiteVectorPolynomialEval p t) := by
  rw [nativeLieRationalFieldPolynomial, finiteVectorPolynomialEval_sum]
  simp only [nativeLieRationalDefectPowerPolynomial_eval, nativeLieLogarithmVectorField,
    nativeLieDexpFiniteInverse, _root_.sum_apply]

omit [CompleteSpace E] [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G] in
 theorem nativeLieRationalDefectPowerPolynomial_coefficients_mem
    (V : Submodule ℚ E)
    (hB : ∀ v ∈ V, ∀ w ∈ V, nativeLieAdjointDifferential (I := I) (G := G) v w ∈ V)
    {p q : List (ℕ × E)} (hp : finiteVectorPolynomialCoefficientsMem V p)
    (hq : finiteVectorPolynomialCoefficientsMem V q) (n : ℕ) :
    finiteVectorPolynomialCoefficientsMem V
      (nativeLieRationalDefectPowerPolynomial (I := I) (G := G) p q n) := by
  induction n with
  | zero => exact hq
  | succ n ih => exact nativeLieRationalDefectPolynomial_coefficients_mem V hB hp ih

omit [CompleteSpace E] [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G] in
 theorem nativeLieRationalFieldPolynomial_coefficients_mem
    (V : Submodule ℚ E)
    (hB : ∀ v ∈ V, ∀ w ∈ V, nativeLieAdjointDifferential (I := I) (G := G) v w ∈ V)
    {p q : List (ℕ × E)} (hp : finiteVectorPolynomialCoefficientsMem V p)
    (hq : finiteVectorPolynomialCoefficientsMem V q) :
    finiteVectorPolynomialCoefficientsMem V
      (nativeLieRationalFieldPolynomial (I := I) (G := G) p q) := by
  apply finiteVectorPolynomialCoefficientsMem_sum
  intro n _
  exact nativeLieRationalDefectPowerPolynomial_coefficients_mem V hB hp hq n

end Hindman168
