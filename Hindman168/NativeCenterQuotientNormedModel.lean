import Hindman168.NativeCenterQuotientHomeomorph
import Hindman168.ClosedFiniteRealQuotientSection

/-! The actual original adjoint-kernel center model is closed, so its
actual real quotient has the canonical separated normed vector structure.
The original quotient's section is constructed, not added as a premise. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

instance nativeLieCenterModel_closed :
    IsClosed (nativeLieCenterModel (I := I) (G := G) : Set E) :=
  (nativeLieAdjointDifferential (I := I) (G := G)).isClosed_ker

variable [FiniteDimensional ℝ E]

noncomputable def nativeCenterQuotientProjection :
    E →L[ℝ] E ⧸ nativeLieCenterModel (I := I) (G := G) :=
  finiteRealQuotientProjection (nativeLieCenterModel (I := I) (G := G))

noncomputable def nativeCenterQuotientSection :
    (E ⧸ nativeLieCenterModel (I := I) (G := G)) →L[ℝ] E :=
  finiteRealQuotientSection (nativeLieCenterModel (I := I) (G := G))

omit [CompleteSpace E] [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] in
theorem nativeCenterQuotientSection_right (x : E ⧸ nativeLieCenterModel (I := I) (G := G)) :
    nativeCenterQuotientProjection (I := I) (G := G)
      (nativeCenterQuotientSection (I := I) (G := G) x) = x :=
  finiteRealQuotientSection_right _ x

end Hindman168
