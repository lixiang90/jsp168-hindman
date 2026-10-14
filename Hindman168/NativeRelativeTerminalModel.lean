import Hindman168.NativeDiagonalLayerExponential

/-! The ACTUAL terminal diagonal subspace is inside ACTUAL original
relative native model. Its Exp membership identifies SAME internal terminal. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRelativeTerminalModel {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (d : ℕ) (hd : 0 < d) : Submodule ℝ (nativeRelativeSquareData D d hd 1).E :=
  (diagonalLinearModel (nativeLieLowerCentralModel (I := D.I) (G := D.G) (((s*d) ⌈/⌉ d)-1))).comap
    (nativeRelativeModelInclusion D d hd 1).toLinearMap

theorem native_relative_terminal_model_closed {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (d : ℕ) (hd : 0 < d) :
    IsClosed (nativeRelativeTerminalModel D d hd : Set (nativeRelativeSquareData D d hd 1).E) :=
  (nativeRelativeTerminalModel D d hd).closed_of_finiteDimensional

theorem native_relative_terminal_exponential_mem_iff {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (v : (nativeRelativeSquareData D d hd 1).E) :
    nativeLieExponential (E := (nativeRelativeSquareData D d hd 1).E)
      (I := (nativeRelativeSquareData D d hd 1).I) (G := (nativeRelativeSquareData D d hd 1).G) v ∈
        nativeRelativeSquareInternalFiltration D d (s*d) ↔ v ∈ nativeRelativeTerminalModel D d hd := by
  have ht := relative_square_internal_terminal_diagonal
    (roughStretchedLowerCentralFiltration D.G d) (rough_stretched_filtration_normal d) (s*d)
    (rough_stretched_filtration_terminal d hd D.step_le)
  have hm := congrArg (fun K : Subgroup (nativeRelativeSquareData D d hd 1).G =>
    nativeLieExponential (E := (nativeRelativeSquareData D d hd 1).E)
      (I := (nativeRelativeSquareData D d hd 1).I) (G := (nativeRelativeSquareData D d hd 1).G) v ∈ K) ht
  have he := congrArg (fun p : D.G × D.G =>
    p ∈ relativeDiagonalSubgroup (roughStretchedLowerCentralFiltration D.G d (s*d)))
      (native_relative_data_exponential D d hd 1 v)
  exact (Iff.of_eq hm).trans ((Iff.of_eq he).trans
    (native_diagonal_layer_exponential_mem_iff D d (s*d) (nativeRelativeModelInclusion D d hd 1 v)))

end Hindman168
