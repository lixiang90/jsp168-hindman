import Hindman168.NativeRationalFilteredRelativeSquare
import Hindman168.SubgroupStructureTransport
import Hindman168.NativeLieSubalgebraLieGroup

/-! Genuine native structures and original lattice quotient for arbitrary finite rational Lie-filtered relative layers. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

@[reducible]
noncomputable def nativeRationalRelativeChartedSpace {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    ChartedSpace (nativeLieSubalgebraModel (nativeRationalRelativeNativeSubalgebra D F i))
      (nativeRationalRelativeGroupLayer D F i) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  exact subgroupChartedSpaceOfEq _ _ (native_rational_relative_native_subgroup_eq D F i)
    (nativeLieSubalgebraChartedSpace (nativeRationalRelativeNativeSubalgebra D F i))

theorem native_rational_relative_lieGroup {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    letI := nativeRationalRelativeChartedSpace D F i
    LieGroup 𝓘(ℝ,nativeLieSubalgebraModel (nativeRationalRelativeNativeSubalgebra D F i)) ∞
      (nativeRationalRelativeGroupLayer D F i) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  exact subgroup_lieGroup_of_eq _ _ _ (native_rational_relative_native_subgroup_eq D F i)
    (nativeLieSubalgebraChartedSpace (nativeRationalRelativeNativeSubalgebra D F i))
    (nativeLieSubalgebra_lieGroup (nativeRationalRelativeNativeSubalgebra D F i))

theorem native_rational_relative_boundaryless {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    letI := nativeRationalRelativeChartedSpace D F i
    BoundarylessManifold 𝓘(ℝ,nativeLieSubalgebraModel (nativeRationalRelativeNativeSubalgebra D F i))
      (nativeRationalRelativeGroupLayer D F i) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  exact subgroup_boundaryless_of_eq _ _ _ (native_rational_relative_native_subgroup_eq D F i)
    (nativeLieSubalgebraChartedSpace (nativeRationalRelativeNativeSubalgebra D F i))
    (nativeLieSubalgebra_boundaryless (nativeRationalRelativeNativeSubalgebra D F i))

end Hindman168
