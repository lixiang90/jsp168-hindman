import Hindman168.NativeRelativeTerminalRational

/-! ACTUAL ORIGINAL terminal layer model for Fourier on ORIGINAL
G/Gamma, separately from the paired relative group's terminal diagonal. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeOriginalTerminalModel {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) : Submodule ℝ D.E :=
  nativeLieLowerCentralModel (I := D.I) (G := D.G) (((s*d) ⌈/⌉ d)-1)

theorem native_original_terminal_group_le_center {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    roughStretchedLowerCentralFiltration D.G d (s*d) ≤ Subgroup.center D.G := by
  intro z hz
  have hp := (relative_diagonal_mem_iff (roughStretchedLowerCentralFiltration D.G d (s*d)) (z,z)).mpr ⟨hz,rfl⟩
  have hc := relative_terminal_diagonal_le_center (roughStretchedLowerCentralFiltration D.G d)
    (rough_stretched_filtration_conditions d hd) (rough_stretched_filtration_one d hd) (s*d)
    (rough_stretched_filtration_terminal d hd D.step_le) hp
  apply Subgroup.mem_center_iff.mpr
  intro g
  exact congrArg Prod.fst (Subgroup.mem_center_iff.mp hc (g,1))

theorem native_original_terminal_model_le_center {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    nativeOriginalTerminalModel D d ≤ nativeLieCenterModel (I := D.I) (G := D.G) := by
  intro v hv
  apply (nativeLieExponential_mem_center_iff_mem_centerModel (I := D.I) (G := D.G) v).mp
  exact native_original_terminal_group_le_center D d hd
    ((rough_native_stretched_filtration_exp_mem_iff (I := D.I) d (s*d) v).mpr hv)

theorem native_original_terminal_model_rational {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) :
    nativeLatticeRationalSubspace (E := D.E) (I := D.I) D.Γ (nativeOriginalTerminalModel D d) :=
  nativeLieLowerCentralModel_lattice_rational (I := D.I) D.Γ (((s*d) ⌈/⌉ d)-1)

theorem native_original_terminal_central_subgroup_eq {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    nativeCentralSubspaceSubgroup (I := D.I) (nativeOriginalTerminalModel D d)
      (native_original_terminal_model_le_center D d hd) = roughStretchedLowerCentralFiltration D.G d (s*d) := by
  ext g
  exact (nativeCentralSubspaceSubgroup_mem_logarithm (I := D.I) _ _ g).trans
    (rough_native_stretched_filtration_mem_log_iff (I := D.I) d (s*d) g).symm

end Hindman168
