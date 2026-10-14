import Hindman168.RoughSpatialSubstitution
import Hindman168.RoughNativeKernelLogPolynomial

namespace Hindman168
open MvPolynomial
open scoped Manifold ContDiff

variable {κ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_affine_kernel_coordinates
    (V : E) (a m : MvPolynomial (Option κ) ℝ)
    (p : RoughVectorMvPolynomial (Option κ) E) (P : (Option κ → ℝ) → G)
    (hp : ∀ x, roughVectorMvEval p x = nativeLieGlobalLogarithm (E := E) (I := I) (P x))
    (d : ℕ) (ha : a.totalDegree ≤ d) (hm : m.totalDegree ≤ d)
    (hd : RoughVectorMvDegreeLE p d) (ell : E →ₗ[ℝ] ℝ) (u : κ → ℝ) (K : ℝ) :
    ∃ q : MvPolynomial (Option κ) ℝ,
      q.totalDegree ≤ ((((Group.nilpotencyClass G * Group.nilpotencyClass G + 1) ^
        (Group.nilpotencyClass G + 1)) ^ 2) * d) ∧
      ∀ (z : ℝ) (y : κ → ℝ),
        let x : Option κ → ℝ := fun t => t.elim z (fun j => u j + K * y j)
        eval (Option.elim · z y) q = ell (nativeLieGlobalLogarithm (E := E) (I := I)
          (roughNativeKernelFactor (I := I) V (eval x a) (eval x m) (P x))) := by
  obtain ⟨q, hq, he⟩ := roughNativeKernelLogPolynomial_coordinate V a m p P hp d ha hm hd ell
  refine ⟨roughSpatialSubstitution u K q,
    (roughSpatialSubstitution_degree u K q).trans hq, ?_⟩
  intro z y
  rw [roughSpatialSubstitution_eval]
  exact he _

end Hindman168
