import Hindman168.NativeRelativeLieLayerRational
import Hindman168.NativeRelativeReductionRationalSpan
import Hindman168.NativeRelativeReducedLieFiltration

/-! Every actual image Lie layer is rational against the SAME actual
image lattice. Entire real spans are transported, not just generators. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_relative_reduced_layer_rational {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    nativeLatticeRationalSubspace (E := (nativeRelativeReducedData D d hd).E)
      (I := (nativeRelativeReducedData D d hd).I) (nativeRelativeReducedData D d hd).Γ
        (nativeRelativeReducedLieFiltration D d hd i) :=
  rational_real_span_map (nativeRelativeReductionModelProjection D d hd).toLinearMap
    (nativeRelativeLieFiltration D d hd i)
    (nativeSubgroupRationalLogSpan (E := (nativeRelativeSquareData D d hd 1).E)
      (I := (nativeRelativeSquareData D d hd 1).I) (nativeRelativeSquareData D d hd 1).Γ)
    (nativeSubgroupRationalLogSpan (E := (nativeRelativeReducedData D d hd).E)
      (I := (nativeRelativeReducedData D d hd).I) (nativeRelativeReducedData D d hd).Γ)
    (fun _ hv => native_relative_reduction_rational_mem D d hd hv)
    (native_relative_lie_layer_rational D d hd i)

end Hindman168
