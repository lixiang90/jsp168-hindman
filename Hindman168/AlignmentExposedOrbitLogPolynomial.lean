import Hindman168.NativeLieMultivariateOrbitLog
import Hindman168.RationalPolynomialRealTransfer
import Hindman168.AlignmentExposedCubeEvaluation

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

noncomputable def alignmentExposedOrbitLogPolynomial {n : ℕ} (F : MasterParameterFamily)
    (q₀ w : ℕ) (i : Fin n) (T : Finset (Fin n)) (x : Fin n → ℕ)
    (v : AlignmentAddingPair n i → ℤ) (g b : G) (ell : E →ₗ[ℝ] ℝ) :
    MvPolynomial (Option (Option (AlignmentAddingPair n i))) ℝ :=
  nativeLieMultivariateOrbitLog (I := I) g b ell
    (MvPolynomial.map (Rat.castHom ℝ) (alignmentExposedCubePolynomial F q₀ w i T x v))

theorem alignmentExposedOrbitLogPolynomial_degree {n : ℕ} (F : MasterParameterFamily)
    (q₀ w : ℕ) (i : Fin n) (T : Finset (Fin n)) (x : Fin n → ℕ)
    (v : AlignmentAddingPair n i → ℤ) (g b : G) (ell : E →ₗ[ℝ] ℝ)
    (s : ℕ) (hs : Group.nilpotencyClass G ≤ s) :
    (alignmentExposedOrbitLogPolynomial (I := I) F q₀ w i T x v g b ell).totalDegree ≤
      ((s * s + 1) ^ (s + 1)) * 2 := by
  apply nativeLieMultivariateOrbitLog_degree _ _ _ _ s 2 hs
  exact (rationalPolynomial_real_degree _).trans (alignmentExposedCubePolynomial_degree F q₀ w i T x v)

theorem alignmentExposedOrbitLogPolynomial_eval {n : ℕ} (F : MasterParameterFamily)
    (q₀ w : ℕ) (i : Fin n) (T : Finset (Fin n)) (x : Fin n → ℕ)
    (v : AlignmentAddingPair n i → ℤ) (g b : G) (ell : E →ₗ[ℝ] ℝ)
    (z : Option (Option (AlignmentAddingPair n i)) → ℚ) (k : ℤ)
    (hk : MvPolynomial.eval z (alignmentExposedCubePolynomial F q₀ w i T x v) = (k : ℚ)) :
    MvPolynomial.eval (fun j => (z j : ℝ))
      (alignmentExposedOrbitLogPolynomial (I := I) F q₀ w i T x v g b ell) =
      ell (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) (g ^ k * b)) := by
  apply nativeLieMultivariateOrbitLog_eval _ _ _ _ _ k
  rw [rationalPolynomial_real_eval, hk]
  norm_cast

theorem alignmentExposedOrbitLogPolynomial_frozen
    {n d : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F)
    (q₀ w : ℕ) (i : Fin n) (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i)
    {x y : Fin n → ℕ} (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hkey : alignmentShortExposureKey F w i T x = alignmentShortExposureKey F w i T y)
    (v : AlignmentAddingPair n i → ℤ) (g b : G) (ell : E →ₗ[ℝ] ℝ) :
    alignmentExposedOrbitLogPolynomial (I := I) F q₀ w i T x v g b ell =
      alignmentExposedOrbitLogPolynomial (I := I) F q₀ w i T y v g b ell := by
  unfold alignmentExposedOrbitLogPolynomial
  rw [alignmentExposedCubePolynomial_frozen hF q₀ w i T hT hx hy hkey v]

end Hindman168
