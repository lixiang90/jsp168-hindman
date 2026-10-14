import Hindman168.NativeRationalRelativeData
import Hindman168.SubgroupInclusionTransport
import Hindman168.NativeLieSubalgebraNativeCoordinates

/-! Actual native inclusion and Exp/Log compatibility for arbitrary rational relative layers. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalRelativeGroupInclusion {s ℓ : ℕ} (D : NativeNilmanifoldData.{u} s)
    (F : NativeRationalLieFiltration D ℓ) (i : ℕ) : (nativeRationalRelativeData D F i).G →* (D.G × D.G) :=
  (nativeRationalRelativeGroupLayer D F i).subtype

noncomputable def nativeRationalRelativeModelInclusion {s ℓ : ℕ} (D : NativeNilmanifoldData.{u} s)
    (F : NativeRationalLieFiltration D ℓ) (i : ℕ) : (nativeRationalRelativeData D F i).E →L[ℝ] (D.E × D.E) :=
  (nativeLieSubalgebraModel (nativeRationalRelativeNativeSubalgebra D F i)).subtype.toContinuousLinearMap

theorem native_rational_relative_inclusion_contMDiff {s ℓ : ℕ} (D : NativeNilmanifoldData.{u} s)
    (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    ContMDiff (nativeRationalRelativeData D F i).I (D.I.prod D.I) ∞
      (nativeRationalRelativeGroupInclusion D F i) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  exact subgroup_inclusion_contMDiff_of_eq _ _ _ _
    (native_rational_relative_native_subgroup_eq D F i)
    (nativeLieSubalgebraChartedSpace (nativeRationalRelativeNativeSubalgebra D F i))
    (nativeLieSubalgebra_inclusion_contMDiff (nativeRationalRelativeNativeSubalgebra D F i))

theorem native_rational_relative_inclusion_mfderiv {s ℓ : ℕ} (D : NativeNilmanifoldData.{u} s)
    (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    mfderiv (nativeRationalRelativeData D F i).I (D.I.prod D.I)
      (nativeRationalRelativeGroupInclusion D F i) 1 = nativeRationalRelativeModelInclusion D F i := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  exact subgroup_inclusion_mfderiv_of_eq _ _ _ _
    (native_rational_relative_native_subgroup_eq D F i)
    (nativeLieSubalgebraChartedSpace (nativeRationalRelativeNativeSubalgebra D F i)) _
    (nativeLieSubalgebra_inclusion_mfderiv (nativeRationalRelativeNativeSubalgebra D F i))

end Hindman168
