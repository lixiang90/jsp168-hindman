import Hindman168.NativeRelativeTerminalCenter

/-! SAME ORIGINAL internal terminal layer, explicitly typed in ACTUAL
relative NativeData group. This preserves literal subgroup operations. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

def nativeRelativeTerminalSubgroup {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (d : ℕ) (hd : 0 < d) : Subgroup (nativeRelativeSquareData D d hd 1).G :=
  nativeRelativeSquareInternalFiltration D d (s*d)

theorem native_relative_terminal_subgroup_original {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    nativeRelativeTerminalSubgroup D d hd = nativeRelativeSquareInternalFiltration D d (s*d) := rfl

theorem native_relative_terminal_subgroup_normal {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    (nativeRelativeTerminalSubgroup D d hd).Normal :=
  native_relative_square_internal_terminal_normal D d hd

theorem native_relative_terminal_subgroup_central_eq {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    nativeCentralSubspaceSubgroup (E := (nativeRelativeSquareData D d hd 1).E)
      (I := (nativeRelativeSquareData D d hd 1).I) (G := (nativeRelativeSquareData D d hd 1).G)
      (nativeRelativeTerminalModel D d hd) (native_relative_terminal_model_le_center D d hd) =
        nativeRelativeTerminalSubgroup D d hd :=
  native_relative_terminal_central_subgroup_eq D d hd

end Hindman168
