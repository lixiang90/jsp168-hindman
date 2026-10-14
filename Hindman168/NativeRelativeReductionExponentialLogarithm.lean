import Hindman168.NativeRelativeReductionProjection
import Hindman168.LieExponentialHomomorphism

/-! ACTUAL relative terminal-quotient native Exp/Log compatibility,
using genuine smooth-hom ODE uniqueness and actual identity derivative. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_relative_reduction_data_exponential {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (v : (nativeRelativeSquareData D d hd 1).E) :
    nativeRelativeReductionGroupProjection D d hd
      (nativeLieExponential (E := (nativeRelativeSquareData D d hd 1).E)
        (I := (nativeRelativeSquareData D d hd 1).I) (G := (nativeRelativeSquareData D d hd 1).G) v) =
      nativeLieExponential (E := (nativeRelativeReducedData D d hd).E)
        (I := (nativeRelativeReducedData D d hd).I) (G := (nativeRelativeReducedData D d hd).G)
        (nativeRelativeReductionModelProjection D d hd v) := by
  have h := nativeLieExponential_map (I := (nativeRelativeSquareData D d hd 1).I)
    (J := (nativeRelativeReducedData D d hd).I) (nativeRelativeReductionGroupProjection D d hd)
    ((native_relative_reduction_projection_contMDiff D d hd).mdifferentiable (by norm_num)) v
  rw [native_relative_reduction_projection_mfderiv] at h
  exact h

theorem native_relative_reduction_data_logarithm {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (g : (nativeRelativeSquareData D d hd 1).G) :
    nativeLieGlobalLogarithm (E := (nativeRelativeReducedData D d hd).E)
      (I := (nativeRelativeReducedData D d hd).I) (G := (nativeRelativeReducedData D d hd).G)
      (nativeRelativeReductionGroupProjection D d hd g) =
    nativeRelativeReductionModelProjection D d hd
      (nativeLieGlobalLogarithm (E := (nativeRelativeSquareData D d hd 1).E)
        (I := (nativeRelativeSquareData D d hd 1).I) (G := (nativeRelativeSquareData D d hd 1).G) g) := by
  have h := native_relative_reduction_data_exponential D d hd
    (nativeLieGlobalLogarithm (E := (nativeRelativeSquareData D d hd 1).E)
      (I := (nativeRelativeSquareData D d hd 1).I) (G := (nativeRelativeSquareData D d hd 1).G) g)
  rw [nativeLieExponential_globalLogarithm] at h
  have hl := congrArg (nativeLieGlobalLogarithm (E := (nativeRelativeReducedData D d hd).E)
    (I := (nativeRelativeReducedData D d hd).I) (G := (nativeRelativeReducedData D d hd).G)) h
  rw [nativeLieGlobalLogarithm_exponential] at hl
  exact hl

end Hindman168
