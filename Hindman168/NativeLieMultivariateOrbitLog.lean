import Hindman168.VectorPolynomialMultivariateProjection
import Hindman168.NativeLieOrbitLogPolynomial

namespace Hindman168
open scoped Manifold ContDiff

variable {E σ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

noncomputable def nativeLieMultivariateOrbitLog (g x : G) (ell : E →ₗ[ℝ] ℝ)
    (P : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  vectorPolynomialMultivariateProjection ell P (nativeLieOrbitLogPolynomial (E := E) (I := I) g x)

theorem nativeLieMultivariateOrbitLog_degree (g x : G) (ell : E →ₗ[ℝ] ℝ)
    (P : MvPolynomial σ ℝ) (s d : ℕ) (hs : Group.nilpotencyClass G ≤ s) (hP : P.totalDegree ≤ d) :
    (nativeLieMultivariateOrbitLog (I := I) g x ell P).totalDegree ≤
      ((s * s + 1) ^ (s + 1)) * d := by
  exact (vectorPolynomialMultivariateProjection_degree ell P _ _
    (nativeLieOrbitLogPolynomial_degree g x s hs)).trans (Nat.mul_le_mul_left _ hP)

theorem nativeLieMultivariateOrbitLog_eval (g x : G) (ell : E →ₗ[ℝ] ℝ)
    (P : MvPolynomial σ ℝ) (z : σ → ℝ) (k : ℤ) (hk : MvPolynomial.eval z P = (k : ℝ)) :
    MvPolynomial.eval z (nativeLieMultivariateOrbitLog (I := I) g x ell P) =
      ell (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) (g ^ k * x)) := by
  rw [nativeLieMultivariateOrbitLog, vectorPolynomialMultivariateProjection_eval,
    hk, nativeLieOrbitLogPolynomial_eval]

end Hindman168
