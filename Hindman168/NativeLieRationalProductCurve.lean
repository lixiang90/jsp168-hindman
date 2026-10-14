import Hindman168.NativeLieRationalAdjoint

/-! An explicit finite rational polynomial represents the genuine
original logarithm of Exp(u)*Exp(t*w) for every real t. Its endpoint is
the actual original product logarithm. The finite recursive coefficient
construction uses only original brackets and rational scalars; no matrix
embedding, formal BCH identity or logarithm inverse is supplied. -/

namespace Hindman168
open Function Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeLieRationalProductPolynomial (u w : E) : List (ℕ × E) :=
  nativeLieRationalPicardPolynomial (I := I) (G := G) w u (Group.nilpotencyClass G + 1)

 theorem nativeLieRationalProductPolynomial_eval (u w : E) (t : ℝ) :
    finiteVectorPolynomialEval (nativeLieRationalProductPolynomial (I := I) (G := G) u w) t =
      nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
        (nativeLieExponential (I := I) (G := G) u * lieOneParameterCurve (I := I) (G := G) w t) := by
  let exp : E → G := fun v => nativeLieExponential (I := I) (G := G) v
  let log : G → E := nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
  let z : E := nativeLieLogarithmLift (E := E) (I := I) (G := G) w u t
  have he : exp z = exp u * lieOneParameterCurve (I := I) (G := G) w t :=
    nativeLieExponential_logarithmLift (E := E) (I := I) (G := G) w u t
  rw [nativeLieRationalProductPolynomial, nativeLieRationalPicardPolynomial_eval]
  change z = log (exp u * lieOneParameterCurve (I := I) (G := G) w t)
  rw [← he]
  exact (nativeLieGlobalLogarithm_exponential (E := E) (I := I) (G := G) z).symm

 theorem nativeLieRationalProductPolynomial_endpoint (u w : E) :
    finiteVectorPolynomialEval (nativeLieRationalProductPolynomial (I := I) (G := G) u w) 1 =
      nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
        (nativeLieExponential (I := I) (G := G) u * nativeLieExponential (I := I) (G := G) w) :=
  nativeLieRationalProductPolynomial_eval (I := I) (G := G) u w 1

omit [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G] [Group.IsNilpotent G] in
 theorem nativeLieRationalProductPolynomial_coefficients_mem
    (V : Submodule ℚ E) (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V)
    {u w : E} (hu : u ∈ V) (hw : w ∈ V) :
    finiteVectorPolynomialCoefficientsMem V
      (nativeLieRationalProductPolynomial (I := I) (G := G) u w) :=
  nativeLieRationalPicardPolynomial_coefficients_mem V
    (fun _ hv _ hw => nativeLieAdjointDifferential_mem_rational V hbr hv hw) hw hu _

end Hindman168
