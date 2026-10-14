import Hindman168.NativeLieSubalgebraNativeCoordinates
import Hindman168.RoughVectorMvLinearMap

namespace Hindman168
open scoped Manifold ContDiff
attribute [local instance] lieGroup_smooth_min_three

variable {σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

noncomputable def roughNativeSubgroupLogPolynomial
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (p : RoughVectorMvPolynomial σ E) :
    RoughVectorMvPolynomial σ (nativeLieSubalgebraModel (E := E) S) :=
  roughVectorMvLinearMap (finiteRealSubmoduleRetraction (nativeLieSubalgebraModel (E := E) S)).toLinearMap p

omit [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [ConnectedSpace G] [SimplyConnectedSpace G] in
theorem roughNativeSubgroupLogPolynomial_degree
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) {p : RoughVectorMvPolynomial σ E} {d : ℕ}
    (hp : RoughVectorMvDegreeLE p d) :
    RoughVectorMvDegreeLE (roughNativeSubgroupLogPolynomial S p) d :=
  roughVectorMvLinearMap_degree _ hp

theorem roughNativeSubgroupLogPolynomial_eval
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (p : RoughVectorMvPolynomial σ E)
    (Q : (σ → ℝ) → nativeLieSubalgebraSubgroup (E := E) S)
    (hp : ∀ x, roughVectorMvEval p x = nativeLieGlobalLogarithm (E := E) (I := I) (Q x).val) :
    letI := nativeLieSubalgebraChartedSpace (E := E) S
    letI := nativeLieSubalgebra_lieGroup S
    letI := nativeLieSubalgebra_boundaryless S
    letI := nativeLieSubalgebraSubgroup_connected S
    letI := nativeLieSubalgebraSubgroup_simplyConnected S
    ∀ x, roughVectorMvEval (roughNativeSubgroupLogPolynomial S p) x =
      nativeLieGlobalLogarithm (E := nativeLieSubalgebraModel (E := E) S)
        (I := 𝓘(ℝ, nativeLieSubalgebraModel (E := E) S)) (Q x) := by
  letI := nativeLieSubalgebraChartedSpace (E := E) S
  letI := nativeLieSubalgebra_lieGroup S
  letI := nativeLieSubalgebra_boundaryless S
  letI := nativeLieSubalgebraSubgroup_connected S
  letI := nativeLieSubalgebraSubgroup_simplyConnected S
  intro x
  rw [roughNativeSubgroupLogPolynomial, roughVectorMvLinearMap_eval, hp x]
  rw [← nativeLieSubalgebra_native_logarithm S (Q x)]
  exact finiteRealSubmoduleRetraction_left _ _

theorem roughNativeSubgroupLogPolynomial_coordinates
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (p : RoughVectorMvPolynomial σ E)
    (Q : (σ → ℝ) → nativeLieSubalgebraSubgroup (E := E) S)
    (hp : ∀ x, roughVectorMvEval p x = nativeLieGlobalLogarithm (E := E) (I := I) (Q x).val)
    (d : ℕ) (hd : RoughVectorMvDegreeLE p d)
    (ell : nativeLieSubalgebraModel (E := E) S →ₗ[ℝ] ℝ) :
    letI := nativeLieSubalgebraChartedSpace (E := E) S
    letI := nativeLieSubalgebra_lieGroup S
    letI := nativeLieSubalgebra_boundaryless S
    letI := nativeLieSubalgebraSubgroup_connected S
    letI := nativeLieSubalgebraSubgroup_simplyConnected S
    ∃ q : MvPolynomial σ ℝ, q.totalDegree ≤ d ∧ ∀ x, MvPolynomial.eval x q =
      ell (nativeLieGlobalLogarithm (E := nativeLieSubalgebraModel (E := E) S)
        (I := 𝓘(ℝ, nativeLieSubalgebraModel (E := E) S)) (Q x)) := by
  letI := nativeLieSubalgebraChartedSpace (E := E) S
  letI := nativeLieSubalgebra_lieGroup S
  letI := nativeLieSubalgebra_boundaryless S
  letI := nativeLieSubalgebraSubgroup_connected S
  letI := nativeLieSubalgebraSubgroup_simplyConnected S
  refine ⟨roughVectorMvProjection ell (roughNativeSubgroupLogPolynomial S p),
    roughVectorMvProjection_degree ell (roughNativeSubgroupLogPolynomial_degree S hd), ?_⟩
  intro x
  rw [roughVectorMvProjection_eval, roughNativeSubgroupLogPolynomial_eval S p Q hp]

end Hindman168
