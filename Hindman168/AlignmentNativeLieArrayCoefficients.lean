import Hindman168.AlignmentLieArrayEvaluation
import Hindman168.NativeLieGroupNilpotency

/-! Apply the genuine coefficient construction to the original native
Lie algebra. Its finite dimension uses the proved native group-to-Lie
lower-central cutoff, with no supplied replacement filtration. -/

namespace Hindman168
open scoped TensorProduct Manifold ContDiff

variable {σ : Type*}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def alignmentNativeLieArrayCoefficients (σ : Type*)
    (I : ModelWithCorners ℝ E H) (G : Type*) [TopologicalSpace G]
    [ChartedSpace H G] [Group G] [LieGroup I ∞ G] :
    LieSubalgebra ℝ (MvPolynomial σ ℝ ⊗[ℝ] GroupLieAlgebra I G) :=
  alignmentLiePolynomialArrays σ ℝ (GroupLieAlgebra I G)

theorem alignmentNativeLieArrayCoefficients_finiteDimensional [Finite σ]
    [FiniteDimensional ℝ E] [Group.IsNilpotent G] :
    FiniteDimensional ℝ (alignmentNativeLieArrayCoefficients σ I G) := by
  letI : FiniteDimensional ℝ (GroupLieAlgebra I G) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  exact alignmentLiePolynomialArrays_finiteDimensional
    (nativeLieLowerCentral_nilpotencyClass_bot (I := I) (G := G))

theorem alignmentNativeLieArrayCoefficients_highDegree_zero [Group.IsNilpotent G]
    (d : σ →₀ ℕ) (x : GroupLieAlgebra I G)
    (hx : x ∈ LieModule.lowerCentralSeries ℝ (GroupLieAlgebra I G)
      (GroupLieAlgebra I G) (d.sum (fun _ n => n) - 1))
    (hd : Group.nilpotencyClass G < d.sum (fun _ n => n)) :
    MvPolynomial.monomial d (1 : ℝ) ⊗ₜ[ℝ] x = 0 :=
  alignmentLieArrayGenerator_highDegree_zero
    (nativeLieLowerCentral_nilpotencyClass_bot (I := I) (G := G)) d x hx hd

end Hindman168
