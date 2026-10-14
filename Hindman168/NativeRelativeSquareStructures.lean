import Hindman168.NativeRelativeSquareExponentialSubgroup
import Hindman168.SubgroupStructureTransport
import Hindman168.NativeLieSubalgebraLieGroup

/-! Genuine native chart/Lie-infinity/boundaryless structures on the
EXACT original relative-square group, via proved exponential subgroup equality. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

@[reducible]
noncomputable def nativeRelativeSquareChartedSpace {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d i : ℕ) :
    ChartedSpace (nativeLieSubalgebraModel (nativeRelativeSquareNativeLieAlgebra D d i))
      (nativeRelativeSquareFiltration D d i) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  exact subgroupChartedSpaceOfEq _ _ (native_relative_square_native_exponential_subgroup D d i)
    (nativeLieSubalgebraChartedSpace (nativeRelativeSquareNativeLieAlgebra D d i))

theorem native_relative_square_lieGroup {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d i : ℕ) :
    letI := nativeRelativeSquareChartedSpace D d i
    LieGroup 𝓘(ℝ,nativeLieSubalgebraModel (nativeRelativeSquareNativeLieAlgebra D d i)) ∞
      (nativeRelativeSquareFiltration D d i) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  exact subgroup_lieGroup_of_eq _ _ _ (native_relative_square_native_exponential_subgroup D d i)
    (nativeLieSubalgebraChartedSpace (nativeRelativeSquareNativeLieAlgebra D d i))
    (nativeLieSubalgebra_lieGroup (nativeRelativeSquareNativeLieAlgebra D d i))

theorem native_relative_square_boundaryless {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d i : ℕ) :
    letI := nativeRelativeSquareChartedSpace D d i
    BoundarylessManifold 𝓘(ℝ,nativeLieSubalgebraModel (nativeRelativeSquareNativeLieAlgebra D d i))
      (nativeRelativeSquareFiltration D d i) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  exact subgroup_boundaryless_of_eq _ _ _ (native_relative_square_native_exponential_subgroup D d i)
    (nativeLieSubalgebraChartedSpace (nativeRelativeSquareNativeLieAlgebra D d i))
    (nativeLieSubalgebra_boundaryless (nativeRelativeSquareNativeLieAlgebra D d i))

end Hindman168
