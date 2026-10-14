import Hindman168.NativeLieFilteredLayerSubalgebra
import Hindman168.NativeRelativeReducedLayerRational

/-! Exact native Lie subalgebras for the actual internal relative and
reduced image group layers. Every generic input comes from original data. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRelativeInternalLieSubalgebra {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    LieSubalgebra ℝ (GroupLieAlgebra (nativeRelativeSquareData D d hd 1).I (nativeRelativeSquareData D d hd 1).G) :=
  nativeLieFilteredLayerSubalgebra (nativeRelativeSquareData D d hd 1)
    (nativeRelativeLieFiltration D d hd) (native_relative_lie_filtration_antitone D d hd)
    (fun _ _ _ _ hv hw => native_relative_lie_filtration_bracket D d hd hv hw) i

noncomputable def nativeRelativeReducedLayerLieSubalgebra {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    LieSubalgebra ℝ (GroupLieAlgebra (nativeRelativeReducedData D d hd).I (nativeRelativeReducedData D d hd).G) :=
  nativeLieFilteredLayerSubalgebra (nativeRelativeReducedData D d hd)
    (nativeRelativeReducedLieFiltration D d hd) (native_relative_reduced_lie_filtration_antitone D d hd)
    (fun _ _ _ _ hv hw => native_relative_reduced_lie_filtration_bracket D d hd hv hw) i

theorem native_relative_internal_subalgebra_model {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    nativeLieSubalgebraModel (nativeRelativeInternalLieSubalgebra D d hd i) = nativeRelativeLieFiltration D d hd i := rfl

theorem native_relative_reduced_subalgebra_model {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    nativeLieSubalgebraModel (nativeRelativeReducedLayerLieSubalgebra D d hd i) =
      nativeRelativeReducedLieFiltration D d hd i := rfl

theorem native_relative_internal_layer_subgroup_eq {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    nativeLieSubalgebraSubgroup (nativeRelativeInternalLieSubalgebra D d hd i) =
      nativeRelativeSquareInternalFiltration D d i :=
  native_lie_filtered_layer_subgroup_eq (nativeRelativeSquareData D d hd 1)
    (nativeRelativeLieFiltration D d hd) (native_relative_lie_filtration_antitone D d hd)
    (fun _ _ _ _ hv hw => native_relative_lie_filtration_bracket D d hd hv hw)
    (nativeRelativeSquareInternalFiltration D d) (native_relative_internal_layer_logarithm_iff D d hd) i

theorem native_relative_reduced_layer_subgroup_eq {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    nativeLieSubalgebraSubgroup (nativeRelativeReducedLayerLieSubalgebra D d hd i) =
      nativeRelativeReducedNativeFiltration D d hd i :=
  native_lie_filtered_layer_subgroup_eq (nativeRelativeReducedData D d hd)
    (nativeRelativeReducedLieFiltration D d hd) (native_relative_reduced_lie_filtration_antitone D d hd)
    (fun _ _ _ _ hv hw => native_relative_reduced_lie_filtration_bracket D d hd hv hw)
    (nativeRelativeReducedNativeFiltration D d hd) (native_relative_reduced_layer_logarithm_iff D d hd) i

end Hindman168
