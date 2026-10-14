import Hindman168.NativeRelativeReducedData

/-! The PROVED reduced relative filtration is NOW on the EXACT actual
reduced NativeData group, with genuine degree drop and both initial layers top. -/

namespace Hindman168
universe u

def nativeRelativeReducedNativeFiltration {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (d : ℕ) (hd : 0 < d) (i : ℕ) : Subgroup (nativeRelativeReducedData D d hd).G := by
  letI := native_relative_square_internal_terminal_normal D d hd
  exact nativeRelativeSquareReducedFiltration D d hd i

theorem native_relative_reduced_native_filtration_conditions {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    CubeGroupFiltration (nativeRelativeReducedNativeFiltration D d hd) := by
  letI := native_relative_square_internal_terminal_normal D d hd
  exact native_relative_square_reduced_filtration_conditions D d hd

theorem native_relative_reduced_native_filtration_zero {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    nativeRelativeReducedNativeFiltration D d hd 0 = ⊤ := by
  letI := native_relative_square_internal_terminal_normal D d hd
  exact native_relative_square_reduced_filtration_zero D d hd

theorem native_relative_reduced_native_filtration_one {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    nativeRelativeReducedNativeFiltration D d hd 1 = ⊤ := by
  letI := native_relative_square_internal_terminal_normal D d hd
  exact native_relative_square_reduced_filtration_one D d hd

theorem native_relative_reduced_native_filtration_terminal {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    nativeRelativeReducedNativeFiltration D d hd (s*d) = ⊥ := by
  letI := native_relative_square_internal_terminal_normal D d hd
  exact native_relative_square_reduced_filtration_terminal D d hd

theorem native_relative_reduced_native_filtration_beyond_terminal {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) (hi : s*d ≤ i) :
    nativeRelativeReducedNativeFiltration D d hd i = ⊥ := by
  apply le_antisymm _ bot_le
  rw [← native_relative_reduced_native_filtration_terminal D d hd]
  exact (native_relative_reduced_native_filtration_conditions D d hd).antitone hi

end Hindman168
