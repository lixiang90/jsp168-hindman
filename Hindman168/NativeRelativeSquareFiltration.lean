import Hindman168.NativeNilmanifoldData
import Hindman168.RoughNativeStretchedFiltration
import Hindman168.RelativeSquareReducedFiltration
import Hindman168.RelativeSquareTopology

/-! ACTUAL original stretched relative squares and genuine algebraic
filtration-degree reduction. The original layers supply all filtration,
normality, terminal and closedness inputs. No relative lattice or inverse
theorem is assumed or asserted. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

def nativeRelativeSquareFiltration {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (d i : ℕ) : Subgroup (D.G × D.G) :=
  relativeSquareFiltration (roughStretchedLowerCentralFiltration D.G d)
    (rough_stretched_filtration_normal d) i

def nativeRelativeSquareInternalFiltration {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (d i : ℕ) : Subgroup (nativeRelativeSquareFiltration D d 1) :=
  relativeSquareInternalFiltration (roughStretchedLowerCentralFiltration D.G d)
    (rough_stretched_filtration_normal d) i

theorem native_relative_square_filtration_conditions {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    CubeGroupFiltration (nativeRelativeSquareFiltration D d) :=
  relative_square_filtration_conditions _ (rough_stretched_filtration_normal d)
    (rough_stretched_filtration_conditions d hd)

theorem native_relative_square_filtration_closed {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d i : ℕ) :
    IsClosed (nativeRelativeSquareFiltration D d i : Set (D.G × D.G)) := by
  letI := rough_stretched_filtration_normal (G := D.G) d (i+1)
  exact relative_square_closed _ _
    (rough_native_stretched_filtration_closed (E := D.E) (I := D.I) d i)
    (rough_native_stretched_filtration_closed (E := D.E) (I := D.I) d (i+1))

theorem native_relative_square_terminal_diagonal {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    nativeRelativeSquareFiltration D d (s*d) =
      relativeDiagonalSubgroup (roughStretchedLowerCentralFiltration D.G d (s*d)) :=
  relative_square_filtration_terminal_diagonal _ _ _
    (rough_stretched_filtration_terminal d hd D.step_le)

theorem native_relative_square_internal_terminal_normal {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    (nativeRelativeSquareInternalFiltration D d (s*d)).Normal :=
  relative_square_internal_terminal_normal _ _
    (rough_stretched_filtration_conditions d hd) (rough_stretched_filtration_one d hd) _
    (rough_stretched_filtration_terminal d hd D.step_le)

def nativeRelativeSquareReducedFiltration {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (d : ℕ) (hd : 0 < d) (i : ℕ) :
    letI := native_relative_square_internal_terminal_normal D d hd
    Subgroup ((nativeRelativeSquareFiltration D d 1) ⧸
      nativeRelativeSquareInternalFiltration D d (s*d)) :=
  relativeSquareReducedFiltration _ _
    (rough_stretched_filtration_conditions d hd) (rough_stretched_filtration_one d hd) _
    (rough_stretched_filtration_terminal d hd D.step_le) i

theorem native_relative_square_reduced_filtration_conditions {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    letI := native_relative_square_internal_terminal_normal D d hd
    CubeGroupFiltration (nativeRelativeSquareReducedFiltration D d hd) :=
  relative_square_reduced_filtration_conditions _ _
    (rough_stretched_filtration_conditions d hd) (rough_stretched_filtration_one d hd) _
    (rough_stretched_filtration_terminal d hd D.step_le)

theorem native_relative_square_reduced_filtration_zero {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    letI := native_relative_square_internal_terminal_normal D d hd
    nativeRelativeSquareReducedFiltration D d hd 0 = ⊤ :=
  relative_square_reduced_filtration_zero _ _
    (rough_stretched_filtration_conditions d hd) (rough_stretched_filtration_one d hd) _
    (rough_stretched_filtration_terminal d hd D.step_le)

theorem native_relative_square_reduced_filtration_one {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    letI := native_relative_square_internal_terminal_normal D d hd
    nativeRelativeSquareReducedFiltration D d hd 1 = ⊤ :=
  relative_square_reduced_filtration_one _ _
    (rough_stretched_filtration_conditions d hd) (rough_stretched_filtration_one d hd) _
    (rough_stretched_filtration_terminal d hd D.step_le)

theorem native_relative_square_reduced_filtration_terminal {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    letI := native_relative_square_internal_terminal_normal D d hd
    nativeRelativeSquareReducedFiltration D d hd (s*d) = ⊥ :=
  relative_square_reduced_filtration_terminal _ _
    (rough_stretched_filtration_conditions d hd) (rough_stretched_filtration_one d hd) _
    (rough_stretched_filtration_terminal d hd D.step_le)

end Hindman168
