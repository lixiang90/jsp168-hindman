import Hindman168.AlignmentLieArrayFiniteEmbedding
import Hindman168.AlignmentLieArrayNilpotence

/-! A finite set of integer inputs determines every coefficient array
of the original native nilpotent Lie group. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {σ : Type*} [Finite σ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]

attribute [local instance] lieGroup_smooth_min_three

theorem alignmentNativeLieArray_finite_integer_embedding :
    ∃ S : Finset (σ → ℤ), Function.Injective
      (alignmentLieArrayFiniteEvaluation (R := ℝ) (L := GroupLieAlgebra I G) S) := by
  letI : FiniteDimensional ℝ (GroupLieAlgebra I G) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  exact alignmentLieArrayFiniteEvaluation_exists_injective
    (nativeLieLowerCentral_nilpotencyClass_bot (I := I) (G := G))

end Hindman168
