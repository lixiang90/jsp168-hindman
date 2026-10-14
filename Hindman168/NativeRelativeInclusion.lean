import Hindman168.NativeRelativeSquareData
import Hindman168.SubgroupInclusionTransport
import Hindman168.NativeLieSubalgebraNativeCoordinates

/-! ACTUAL original relative native group/model inclusions, with genuine
smoothness and EXACT identity derivative equal to original model inclusion. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

def nativeRelativeGroupInclusion {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (d : ℕ) (hd : 0 < d) (i : ℕ) : (nativeRelativeSquareData D d hd i).G →* (D.G × D.G) :=
  (nativeRelativeSquareFiltration D d i).subtype

noncomputable def nativeRelativeModelInclusion {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (d : ℕ) (hd : 0 < d) (i : ℕ) : (nativeRelativeSquareData D d hd i).E →L[ℝ] (D.E × D.E) :=
  (nativeLieSubalgebraModel (nativeRelativeSquareNativeLieAlgebra D d i)).subtype.toContinuousLinearMap

theorem native_relative_inclusion_contMDiff {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (d : ℕ) (hd : 0 < d) (i : ℕ) :
    ContMDiff (nativeRelativeSquareData D d hd i).I (D.I.prod D.I) ∞
      (nativeRelativeGroupInclusion D d hd i) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  exact subgroup_inclusion_contMDiff_of_eq _ _ _ _
    (native_relative_square_native_exponential_subgroup D d i)
    (nativeLieSubalgebraChartedSpace (nativeRelativeSquareNativeLieAlgebra D d i))
    (nativeLieSubalgebra_inclusion_contMDiff (nativeRelativeSquareNativeLieAlgebra D d i))

theorem native_relative_inclusion_mfderiv {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (d : ℕ) (hd : 0 < d) (i : ℕ) :
    mfderiv (nativeRelativeSquareData D d hd i).I (D.I.prod D.I)
      (nativeRelativeGroupInclusion D d hd i) 1 = nativeRelativeModelInclusion D d hd i := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  exact subgroup_inclusion_mfderiv_of_eq _ _ _ _
    (native_relative_square_native_exponential_subgroup D d i)
    (nativeLieSubalgebraChartedSpace (nativeRelativeSquareNativeLieAlgebra D d i)) _
    (nativeLieSubalgebra_inclusion_mfderiv (nativeRelativeSquareNativeLieAlgebra D d i))

end Hindman168
