import Hindman168.NativeRelativeLieFiltration
import Hindman168.NativeRelativeExponentialLogarithm

/-! ACTUAL relative Lie layers exponentiate into EXACT original internal
relative group layers. Every original inclusion/Exp/model input is proved. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_relative_lie_filtration_exponential_mem {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ)
    {v : (nativeRelativeSquareData D d hd 1).E} (hv : v ∈ nativeRelativeLieFiltration D d hd i) :
    nativeLieExponential (E := (nativeRelativeSquareData D d hd 1).E)
      (I := (nativeRelativeSquareData D d hd 1).I) (G := (nativeRelativeSquareData D d hd 1).G) v ∈
      nativeRelativeSquareInternalFiltration D d i := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  change nativeRelativeGroupInclusion D d hd 1
    (nativeLieExponential (E := (nativeRelativeSquareData D d hd 1).E)
      (I := (nativeRelativeSquareData D d hd 1).I) (G := (nativeRelativeSquareData D d hd 1).G) v) ∈
        nativeRelativeSquareFiltration D d i
  rw [native_relative_data_exponential,← native_relative_square_native_exponential_subgroup D d i]
  apply (nativeLieSubalgebraSubgroup_mem_globalLogarithm_iff
    (E := D.E × D.E) (I := D.I.prod D.I) (G := D.G × D.G)
      (nativeRelativeSquareNativeLieAlgebra D d i) _).mpr
  rw [nativeLieGlobalLogarithm_exponential,native_relative_square_native_model_eq D d i]
  exact hv

end Hindman168
