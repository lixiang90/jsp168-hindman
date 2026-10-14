import Hindman168.AlignmentLieTensorLayers
import Hindman168.AlignmentNativeLieArrayCoefficients

/-! The actual array coefficient Lie algebra has the original model's
lower-central cutoff, including in the native Lie group specialization. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {σ R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

theorem alignmentLiePolynomialArrays_lowerCentral_bot {s : ℕ}
    (hs : LieModule.lowerCentralSeries R L L s = ⊥) :
    LieModule.lowerCentralSeries R (alignmentLiePolynomialArrays σ R L)
      (alignmentLiePolynomialArrays σ R L) s = ⊥ := by
  let f := (alignmentLiePolynomialArrays σ R L).incl
  have hf : Function.Injective f := Subtype.val_injective
  apply LieIdeal.bot_of_map_eq_bot hf
  apply le_antisymm _ bot_le
  have h := LieIdeal.map_lowerCentralSeries_le s (f := f)
  rw [alignmentLieTensor_lowerCentral_bot hs] at h
  exact h

theorem alignmentLiePolynomialArrays_isNilpotent {s : ℕ}
    (hs : LieModule.lowerCentralSeries R L L s = ⊥) :
    LieModule.IsNilpotent (alignmentLiePolynomialArrays σ R L)
      (alignmentLiePolynomialArrays σ R L) :=
  LieModule.IsNilpotent.mk (M := alignmentLiePolynomialArrays σ R L)
    (alignmentLiePolynomialArrays_lowerCentral_bot hs)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

theorem alignmentNativeLieArrayCoefficients_lowerCentral_bot [Group.IsNilpotent G] :
    LieModule.lowerCentralSeries ℝ (alignmentNativeLieArrayCoefficients σ I G)
      (alignmentNativeLieArrayCoefficients σ I G) (Group.nilpotencyClass G) = ⊥ :=
  alignmentLiePolynomialArrays_lowerCentral_bot
    (nativeLieLowerCentral_nilpotencyClass_bot (I := I) (G := G))

end Hindman168
