import Hindman168.NativeRationalFilteredTerminal
import Hindman168.NilNaturalCosetMetric

/-! Actual closed terminal model/subgroup and actual closed quotient image
lattice. The model and image are never replaced by closure or coordinates. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_terminal_model_closed {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    IsClosed (F.layer ℓ : Set D.E) := (F.layer ℓ).closed_of_finiteDimensional

theorem native_rational_terminal_central_subgroup_eq {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    nativeCentralSubspaceSubgroup (E := D.E) (I := D.I) (G := D.G)
      (F.layer ℓ) (native_rational_filtered_terminal_central D F) = nativeRationalTerminalSubgroup D F := rfl

theorem native_rational_terminal_image_lattice_closed {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    letI := native_rational_terminal_subgroup_normal D F
    IsClosed ((D.Γ.map (QuotientGroup.mk' (nativeRationalTerminalSubgroup D F))) :
      Set (D.G ⧸ nativeRationalTerminalSubgroup D F)) := by
  letI := native_rational_terminal_subgroup_normal D F
  letI : IsClosed (nativeRationalTerminalSubgroup D F : Set D.G) :=
    native_rational_terminal_subgroup_closed D F
  letI := native_rational_terminal_image_lattice_discrete D F
  exact Subgroup.isClosed_of_discrete

end Hindman168
