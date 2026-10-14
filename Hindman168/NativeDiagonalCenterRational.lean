import Hindman168.NativeDiagonalLatticeColumns
import Hindman168.NativeLatticeRationalCoordinates

/-! GENUINE rationality of ACTUAL original diagonal-center model against
the ORIGINAL product lattice; actual lattice columns span the entire model. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_diagonal_center_model_rational {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
    nativeLatticeRationalSubspace (E := D.E × D.E) (I := D.I.prod D.I) (G := D.G × D.G)
      (D.Γ.prod D.Γ) (nativeDiagonalCenterModel D) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  unfold nativeLatticeRationalSubspace
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro v hv
    exact hv.1
  · conv_lhs => rw [← native_diagonal_lattice_columns_span D]
    apply Submodule.span_le.mpr
    rintro v ⟨i,rfl⟩
    apply Submodule.subset_span
    exact ⟨native_diagonal_lattice_column_mem_model D i,native_diagonal_lattice_column_rational_mem D i⟩

end Hindman168
