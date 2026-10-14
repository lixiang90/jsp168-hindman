import Hindman168.NativeSubgroupBracketSpan

/-! Rational scalar restriction of the actual original native Lie
algebra. Compatibility is proved from genuine rational/real scalar
compatibility and the original real Lie bracket law. Original group
nilpotency also terminates the actual rational lower central series. -/

namespace Hindman168
open Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable instance nativeLieRationalAlgebra : LieAlgebra ℚ (GroupLieAlgebra I G) := by
  letI : Module ℚ (GroupLieAlgebra I G) := (inferInstance : Module ℚ E)
  exact {
    toModule := inferInstance
    lie_smul := by
      intro q x y
      rw [← Rat.cast_smul_eq_qsmul ℝ q y]
      rw [LieAlgebra.lie_smul]
      exact Rat.cast_smul_eq_qsmul ℝ q (⁅x, y⁆ : GroupLieAlgebra I G) }

def nativeLieRationalSubalgebra (V : Submodule ℚ E)
    (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V) :
    LieSubalgebra ℚ (GroupLieAlgebra I G) where
  toSubmodule := V
  lie_mem' := fun {x y} hx hy => hbr x y hx hy

variable [Group.IsNilpotent G]

 theorem nativeLieRationalLowerCentral_nilpotencyClass_bot :
    LieModule.lowerCentralSeries ℚ (GroupLieAlgebra I G) (GroupLieAlgebra I G)
      (Group.nilpotencyClass G) = ⊥ := by
  apply SetLike.coe_injective
  calc
    _ = (LieModule.lowerCentralSeries ℤ (GroupLieAlgebra I G) (GroupLieAlgebra I G)
      (Group.nilpotencyClass G) : Set (GroupLieAlgebra I G)) :=
      LieModule.coe_lowerCentralSeries_eq_int ℚ _ _ _
    _ = (LieModule.lowerCentralSeries ℝ (GroupLieAlgebra I G) (GroupLieAlgebra I G)
      (Group.nilpotencyClass G) : Set (GroupLieAlgebra I G)) :=
      (LieModule.coe_lowerCentralSeries_eq_int ℝ _ _ _).symm
    _ = _ := by rw [nativeLieLowerCentral_nilpotencyClass_bot (I := I) (G := G)]; rfl

end Hindman168
