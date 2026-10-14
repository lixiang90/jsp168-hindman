import Hindman168.NativeRelativeExponentialLogarithm
import Hindman168.DiagonalLinearModel

/-! The actual original diagonal-layer group membership is EXACT
actual original diagonal-layer model membership under original product Exp. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_diagonal_layer_exponential_mem_iff {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d i : ℕ) (v : D.E × D.E) :
    nativeLieExponential (E := D.E × D.E) (I := D.I.prod D.I) (G := D.G × D.G) v ∈
      relativeDiagonalSubgroup (roughStretchedLowerCentralFiltration D.G d i) ↔
    v ∈ diagonalLinearModel (nativeLieLowerCentralModel (I := D.I) (G := D.G) ((i ⌈/⌉ d)-1)) := by
  rw [nativeProductExponential_eq]
  exact (relative_diagonal_mem_iff _ _).trans
    ((and_congr (rough_native_stretched_filtration_exp_mem_iff (I := D.I) d i v.1)
      (nativeLieExponential_injective (I := D.I) (G := D.G)).eq_iff).trans
        (diagonal_linear_model_mem_iff _ v).symm)

end Hindman168
