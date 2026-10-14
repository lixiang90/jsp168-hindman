import Hindman168.NativeCenterQuotientTangent
import Hindman168.NativeCenterQuotientSeparation
import Hindman168.NativeSmoothHomLieBracket

/-! The actual original real center projection intertwines the actual
original adjoint generators and preserves the actual original native
Lie brackets. The quotient smooth Lie structure is constructed from its
original group and topology, and its genuine derivative is proved pi. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem nativeCenterQuotient_generator_projection (v w : E) :
    letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
    letI := nativeCenterQuotient_t2Space (I := I) (G := G)
    letI := nativeCenterQuotient_lieGroup (I := I) (G := G)
    let F := E ⧸ nativeLieCenterModel (I := I) (G := G)
    let Q := G ⧸ Subgroup.center G
    let π := nativeCenterQuotientProjection (I := I) (G := G)
    π (nativeLieAdjointGenerator (I := I) (G := G) v w) =
      nativeLieAdjointGenerator (I := 𝓘(ℝ, F)) (G := Q) (π v) (π w) := by
  letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
  letI := nativeCenterQuotient_t2Space (I := I) (G := G)
  letI := nativeCenterQuotient_lieGroup (I := I) (G := G)
  let F := E ⧸ nativeLieCenterModel (I := I) (G := G)
  let Q := G ⧸ Subgroup.center G
  let J := 𝓘(ℝ, F)
  let q : G →* Q := QuotientGroup.mk' (Subgroup.center G)
  let P : E →L[ℝ] F := mfderiv I J q 1
  let π : E →L[ℝ] F := nativeCenterQuotientProjection (I := I) (G := G)
  have h := nativeSmoothHom_generator_intertwine (I := I) (J := J) q
    (nativeCenterQuotient_projection_contMDiff (I := I) (G := G)) v w
  change P (nativeLieAdjointGenerator (I := I) (G := G) v w) =
    nativeLieAdjointGenerator (I := J) (G := Q) (P v) (P w) at h
  have hP : P = π := nativeCenterQuotient_mfderiv_eq_projection (I := I) (G := G)
  rw [hP] at h
  exact h

theorem nativeCenterQuotient_bracket_projection (v w : GroupLieAlgebra I G) :
    letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
    letI := nativeCenterQuotient_t2Space (I := I) (G := G)
    letI := nativeCenterQuotient_lieGroup (I := I) (G := G)
    let F := E ⧸ nativeLieCenterModel (I := I) (G := G)
    let Q := G ⧸ Subgroup.center G
    let π := nativeCenterQuotientProjection (I := I) (G := G)
    let v' : GroupLieAlgebra 𝓘(ℝ, F) Q := π v
    let w' : GroupLieAlgebra 𝓘(ℝ, F) Q := π w
    π (⁅v, w⁆ : GroupLieAlgebra I G) = (⁅v', w'⁆ : GroupLieAlgebra 𝓘(ℝ, F) Q) := by
  letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
  letI := nativeCenterQuotient_t2Space (I := I) (G := G)
  letI := nativeCenterQuotient_lieGroup (I := I) (G := G)
  let F := E ⧸ nativeLieCenterModel (I := I) (G := G)
  let Q := G ⧸ Subgroup.center G
  let J := 𝓘(ℝ, F)
  let π : E →L[ℝ] F := nativeCenterQuotientProjection (I := I) (G := G)
  let v' : GroupLieAlgebra J Q := π v
  let w' : GroupLieAlgebra J Q := π w
  have h := nativeCenterQuotient_generator_projection (I := I) (G := G) (show E from v) (show E from w)
  exact (congrArg π (nativeLieAdjointGenerator_eq_native_bracket (I := I) (G := G) v w).symm).trans
    (h.trans (nativeLieAdjointGenerator_eq_native_bracket (I := J) (G := Q) v' w'))

end Hindman168
