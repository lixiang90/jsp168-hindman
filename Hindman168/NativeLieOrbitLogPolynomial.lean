import Hindman168.NativeLiePolynomialDegree
import Mathlib.Algebra.Group.Conj

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

omit [Module ℚ E] [Group.IsNilpotent G] [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G] in
theorem lieOneParameterCurve_int (v : E) (k : ℤ) :
    lieOneParameterCurve (I := I) (G := G) v (k : ℝ) =
      nativeLieExponential (I := I) (G := G) v ^ k := by
  have h := congrArg Additive.toMul ((lieOneParameterHom (I := I) (G := G) v).map_zsmul k (1 : ℝ))
  simpa [lieOneParameterHom, nativeLieExponential, zsmul_eq_mul] using h

noncomputable def nativeLieOrbitLogPolynomial (g x : G) : List (ℕ × E) :=
  nativeLieRationalProductPolynomial (I := I) (G := G)
    (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) x)
    (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) (x⁻¹ * g * x))

theorem nativeLieOrbitLogPolynomial_eval (g x : G) (k : ℤ) :
    finiteVectorPolynomialEval (nativeLieOrbitLogPolynomial (E := E) (I := I) g x) (k : ℝ) =
      nativeLieGlobalLogarithm (E := E) (I := I) (G := G) (g ^ k * x) := by
  rw [nativeLieOrbitLogPolynomial, nativeLieRationalProductPolynomial_eval,
    lieOneParameterCurve_int, nativeLieExponential_globalLogarithm,
    nativeLieExponential_globalLogarithm]
  congr 1
  have he : (x⁻¹ * g * x) ^ k = x⁻¹ * g ^ k * x := by
    simpa only [inv_inv] using (conj_zpow (i := k) (a := x⁻¹) (b := g))
  rw [he]
  group

theorem nativeLieOrbitLogPolynomial_degree (g x : G) (s : ℕ)
    (hs : Group.nilpotencyClass G ≤ s) :
    finiteVectorPolynomialDegreeLE (nativeLieOrbitLogPolynomial (E := E) (I := I) g x)
      ((s * s + 1) ^ (s + 1)) := by
  apply finiteVectorPolynomialDegreeLE_mono (nativeLieRationalProductPolynomial_degree (I := I) (G := G) _ _)
  gcongr
  omega

end Hindman168
