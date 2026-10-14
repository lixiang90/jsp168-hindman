import Hindman168.NativeRelativeReducedLattice
import Hindman168.NilNaturalCosetMetric

/-! ACTUAL compatible metric on original reduced relative image-lattice
quotient, with original topology and actual open quotient map. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

@[reducible]
noncomputable def nativeRelativeReducedMetric {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    letI := native_relative_terminal_subgroup_normal D d hd
    MetricSpace (((nativeRelativeSquareData D d hd 1).G ⧸ nativeRelativeTerminalSubgroup D d hd) ⧸
      (nativeRelativeSquareData D d hd 1).Γ.map (QuotientGroup.mk' (nativeRelativeTerminalSubgroup D d hd))) := by
  letI := native_relative_terminal_subgroup_normal D d hd
  letI : SecondCountableTopology (nativeRelativeSquareData D d hd 1).G :=
    (nativeLieGlobalExponentialHomeomorph (I := (nativeRelativeSquareData D d hd 1).I)
      (G := (nativeRelativeSquareData D d hd 1).G)).symm.secondCountableTopology
  letI : IsClosed (nativeRelativeTerminalSubgroup D d hd : Set (nativeRelativeSquareData D d hd 1).G) :=
    native_relative_terminal_subgroup_closed D d hd
  letI := native_relative_reduced_lattice_discrete D d hd
  letI := native_relative_reduced_lattice_cocompact D d hd
  letI := native_relative_reduced_lattice_closed D d hd
  exact naturalCompactCosetMetric ((nativeRelativeSquareData D d hd 1).Γ.map
    (QuotientGroup.mk' (nativeRelativeTerminalSubgroup D d hd)))

theorem native_relative_reduced_metric_topology {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    letI := native_relative_terminal_subgroup_normal D d hd
    (nativeRelativeReducedMetric D d hd).toUniformSpace.toTopologicalSpace =
      QuotientGroup.instTopologicalSpace ((nativeRelativeSquareData D d hd 1).Γ.map
        (QuotientGroup.mk' (nativeRelativeTerminalSubgroup D d hd))) := by
  letI := native_relative_terminal_subgroup_normal D d hd
  letI : SecondCountableTopology (nativeRelativeSquareData D d hd 1).G :=
    (nativeLieGlobalExponentialHomeomorph (I := (nativeRelativeSquareData D d hd 1).I)
      (G := (nativeRelativeSquareData D d hd 1).G)).symm.secondCountableTopology
  letI : IsClosed (nativeRelativeTerminalSubgroup D d hd : Set (nativeRelativeSquareData D d hd 1).G) :=
    native_relative_terminal_subgroup_closed D d hd
  letI := native_relative_reduced_lattice_discrete D d hd
  letI := native_relative_reduced_lattice_cocompact D d hd
  letI := native_relative_reduced_lattice_closed D d hd
  exact naturalCompactCosetMetric_topology ((nativeRelativeSquareData D d hd 1).Γ.map
    (QuotientGroup.mk' (nativeRelativeTerminalSubgroup D d hd)))

theorem native_relative_reduced_metric_quotientMap {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    letI := native_relative_terminal_subgroup_normal D d hd
    @IsOpenQuotientMap ((nativeRelativeSquareData D d hd 1).G ⧸ nativeRelativeTerminalSubgroup D d hd)
      (((nativeRelativeSquareData D d hd 1).G ⧸ nativeRelativeTerminalSubgroup D d hd) ⧸
        (nativeRelativeSquareData D d hd 1).Γ.map (QuotientGroup.mk' (nativeRelativeTerminalSubgroup D d hd)))
      inferInstance (nativeRelativeReducedMetric D d hd).toUniformSpace.toTopologicalSpace (↑) := by
  letI := native_relative_terminal_subgroup_normal D d hd
  rw [native_relative_reduced_metric_topology]
  exact QuotientGroup.isOpenQuotientMap_mk

end Hindman168
