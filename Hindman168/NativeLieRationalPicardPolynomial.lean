import Hindman168.NativeLieRationalFieldPolynomial

/-! Explicit finite rational polynomial lists for the original actual
Picard iterates. The real evaluations equal the previously constructed
genuine integral curves. All rational coefficients stay in the original
bracket-closed Q-linear structure, without requiring it to be closed. -/

namespace Hindman168
open MeasureTheory
open scoped Interval Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeLieRationalPicardPolynomial (w u : E) : ℕ → List (ℕ × E)
  | 0 => [(0, u)]
  | n + 1 => [(0, u)] ++ finiteVectorPolynomialPrimitive
      (nativeLieRationalFieldPolynomial (I := I) (G := G)
        (nativeLieRationalPicardPolynomial w u n) [(0, w)])

 theorem nativeLieRationalPicardPolynomial_eval (w u : E) (n : ℕ) (t : ℝ) :
    finiteVectorPolynomialEval (nativeLieRationalPicardPolynomial (I := I) (G := G) w u n) t =
      continuousPicardIterate (nativeLieLogarithmVectorField (I := I) (G := G) w) u n t := by
  induction n generalizing t with
  | zero => simp only [nativeLieRationalPicardPolynomial, finiteVectorPolynomialEval_singleton,
      pow_zero, one_smul, continuousPicardIterate]
  | succ n ih =>
    rw [nativeLieRationalPicardPolynomial, finiteVectorPolynomialEval_append,
      finiteVectorPolynomialEval_singleton, pow_zero, one_smul, finiteVectorPolynomialEval_primitive]
    change u + (∫ s in (0 : ℝ)..t, _) = u + (∫ s in (0 : ℝ)..t, _)
    apply congrArg (fun f : ℝ → E => u + ∫ s in (0 : ℝ)..t, f s)
    funext s
    rw [nativeLieRationalFieldPolynomial_eval, finiteVectorPolynomialEval_singleton,
      pow_zero, one_smul, ih]

omit [CompleteSpace E] [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G] in
 theorem nativeLieRationalPicardPolynomial_coefficients_mem
    (V : Submodule ℚ E)
    (hB : ∀ v ∈ V, ∀ w ∈ V, nativeLieAdjointDifferential (I := I) (G := G) v w ∈ V)
    {w u : E} (hw : w ∈ V) (hu : u ∈ V) (n : ℕ) :
    finiteVectorPolynomialCoefficientsMem V
      (nativeLieRationalPicardPolynomial (I := I) (G := G) w u n) := by
  induction n with
  | zero => exact finiteVectorPolynomialCoefficientsMem_singleton V 0 hu
  | succ n ih =>
    rw [nativeLieRationalPicardPolynomial]
    apply finiteVectorPolynomialCoefficientsMem_append V
      (finiteVectorPolynomialCoefficientsMem_singleton V 0 hu)
    apply finiteVectorPolynomialCoefficientsMem_primitive V
    exact nativeLieRationalFieldPolynomial_coefficients_mem V hB ih
      (finiteVectorPolynomialCoefficientsMem_singleton V 0 hw)

 theorem nativeLiePicard_rational_mem
    (V : Submodule ℚ E)
    (hB : ∀ v ∈ V, ∀ w ∈ V, nativeLieAdjointDifferential (I := I) (G := G) v w ∈ V)
    {w u : E} (hw : w ∈ V) (hu : u ∈ V) (n : ℕ) (q : ℚ) :
    continuousPicardIterate (nativeLieLogarithmVectorField (I := I) (G := G) w) u n (q : ℝ) ∈ V := by
  rw [← nativeLieRationalPicardPolynomial_eval (I := I) (G := G) w u n (q : ℝ)]
  exact finiteVectorPolynomialEval_rational_mem V
    (nativeLieRationalPicardPolynomial_coefficients_mem V hB hw hu n) q

 theorem nativeLieLogarithmLift_rational_mem
    (V : Submodule ℚ E)
    (hB : ∀ v ∈ V, ∀ w ∈ V, nativeLieAdjointDifferential (I := I) (G := G) v w ∈ V)
    {w u : E} (hw : w ∈ V) (hu : u ∈ V) (q : ℚ) :
    nativeLieLogarithmLift (E := E) (I := I) (G := G) w u (q : ℝ) ∈ V :=
  nativeLiePicard_rational_mem V hB hw hu (Group.nilpotencyClass G + 1) q

end Hindman168
