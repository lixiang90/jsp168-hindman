import Hindman168.NativeRelativeLieExponentialLayers

/-! Exact logarithmic membership in every original internal relative layer. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_relative_internal_layer_logarithm_iff {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ)
    (g : (nativeRelativeSquareData D d hd 1).G) :
    g ∈ nativeRelativeSquareInternalFiltration D d i ↔
      nativeLieGlobalLogarithm (E := (nativeRelativeSquareData D d hd 1).E)
        (I := (nativeRelativeSquareData D d hd 1).I)
        (G := (nativeRelativeSquareData D d hd 1).G) g ∈ nativeRelativeLieFiltration D d hd i := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  change nativeRelativeGroupInclusion D d hd 1 g ∈ nativeRelativeSquareFiltration D d i ↔ _
  rw [← native_relative_square_native_exponential_subgroup D d i,
    nativeLieSubalgebraSubgroup_mem_globalLogarithm_iff,
    native_relative_square_native_model_eq D d i]
  change _ ↔ nativeRelativeModelInclusion D d hd 1
    (nativeLieGlobalLogarithm (E := (nativeRelativeSquareData D d hd 1).E)
      (I := (nativeRelativeSquareData D d hd 1).I)
      (G := (nativeRelativeSquareData D d hd 1).G) g) ∈ nativeRelativeSquareModel D d i
  rw [native_relative_data_logarithm]

end Hindman168
