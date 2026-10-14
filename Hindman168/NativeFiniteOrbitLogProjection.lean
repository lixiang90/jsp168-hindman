import Hindman168.NativeLieMultivariateOrbitLog
import Mathlib.LinearAlgebra.Pi

namespace Hindman168
open scoped Manifold ContDiff BigOperators Classical

variable {ι σ E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

noncomputable def nativeFiniteOrbitLogProjection (g b : ι → G)
    (ell : (ι → E) →ₗ[ℝ] ℝ) (P : ι → MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  ∑ j, nativeLieMultivariateOrbitLog (I := I) (g j) (b j)
    (ell.comp (LinearMap.single ℝ (fun _ : ι => E) j)) (P j)

theorem nativeFiniteOrbitLogProjection_degree (g b : ι → G)
    (ell : (ι → E) →ₗ[ℝ] ℝ) (P : ι → MvPolynomial σ ℝ)
    (s d : ℕ) (hs : Group.nilpotencyClass G ≤ s) (hP : ∀ j, (P j).totalDegree ≤ d) :
    (nativeFiniteOrbitLogProjection (I := I) g b ell P).totalDegree ≤ ((s * s + 1) ^ (s + 1)) * d := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  exact nativeLieMultivariateOrbitLog_degree _ _ _ _ s d hs (hP j)

theorem nativeFiniteOrbitLogProjection_eval (g b : ι → G)
    (ell : (ι → E) →ₗ[ℝ] ℝ) (P : ι → MvPolynomial σ ℝ)
    (z : σ → ℝ) (k : ι → ℤ) (hk : ∀ j, MvPolynomial.eval z (P j) = (k j : ℝ)) :
    MvPolynomial.eval z (nativeFiniteOrbitLogProjection (I := I) g b ell P) =
      ell (fun j => nativeLieGlobalLogarithm (E := E) (I := I) (G := G) ((g j) ^ (k j) * b j)) := by
  unfold nativeFiniteOrbitLogProjection
  rw [map_sum]
  simp_rw [nativeLieMultivariateOrbitLog_eval _ _ _ _ z _ (hk _)]
  simp only [LinearMap.comp_apply, LinearMap.single_apply]
  rw [← map_sum, Finset.univ_sum_single]

end Hindman168
