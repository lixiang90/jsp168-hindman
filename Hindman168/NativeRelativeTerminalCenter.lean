import Hindman168.NativeRelativeTerminalModel
import Hindman168.NativeCentralSubspaceSubgroup

/-! ACTUAL terminal diagonal model lies in ACTUAL relative native Lie
center, and its exponential subgroup is SAME original internal terminal layer. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_relative_internal_terminal_le_center {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    nativeRelativeSquareInternalFiltration D d (s*d) ≤
      Subgroup.center (nativeRelativeSquareData D d hd 1).G := by
  intro g hg
  have ht := relative_square_internal_terminal_diagonal
    (roughStretchedLowerCentralFiltration D.G d) (rough_stretched_filtration_normal d) (s*d)
    (rough_stretched_filtration_terminal d hd D.step_le)
  have hp := Eq.mp (congrArg (fun K : Subgroup (nativeRelativeSquareData D d hd 1).G => g ∈ K) ht) hg
  have hc := relative_terminal_diagonal_le_center (roughStretchedLowerCentralFiltration D.G d)
    (rough_stretched_filtration_conditions d hd) (rough_stretched_filtration_one d hd) (s*d)
    (rough_stretched_filtration_terminal d hd D.step_le) hp
  apply Subgroup.mem_center_iff.mpr
  intro h
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp hc (nativeRelativeGroupInclusion D d hd 1 h)

theorem native_relative_terminal_model_le_center {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    nativeRelativeTerminalModel D d hd ≤ nativeLieCenterModel
      (I := (nativeRelativeSquareData D d hd 1).I) (G := (nativeRelativeSquareData D d hd 1).G) := by
  intro v hv
  apply (nativeLieExponential_mem_center_iff_mem_centerModel
    (I := (nativeRelativeSquareData D d hd 1).I) (G := (nativeRelativeSquareData D d hd 1).G) v).mp
  exact native_relative_internal_terminal_le_center D d hd
    ((native_relative_terminal_exponential_mem_iff D d hd v).mpr hv)

theorem native_relative_terminal_central_subgroup_eq {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    nativeCentralSubspaceSubgroup (I := (nativeRelativeSquareData D d hd 1).I)
      (nativeRelativeTerminalModel D d hd) (native_relative_terminal_model_le_center D d hd) =
        nativeRelativeSquareInternalFiltration D d (s*d) := by
  ext g
  have he := native_relative_terminal_exponential_mem_iff D d hd
    (nativeLieGlobalLogarithm (E := (nativeRelativeSquareData D d hd 1).E)
      (I := (nativeRelativeSquareData D d hd 1).I) (G := (nativeRelativeSquareData D d hd 1).G) g)
  rw [nativeLieExponential_globalLogarithm] at he
  exact (nativeCentralSubspaceSubgroup_mem_logarithm
    (I := (nativeRelativeSquareData D d hd 1).I) _ _ g).trans he.symm

end Hindman168
