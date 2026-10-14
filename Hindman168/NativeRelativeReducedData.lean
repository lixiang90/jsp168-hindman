import Hindman168.NativeRelativeReducedMetric
import Hindman168.NativeRelativeReducedStructures

/-! GENUINE NativeData for EXACT original relative group modulo SAME
internal terminal diagonal, actual model quotient/image lattice/metric.
Same step bound s; the separately proved decrease is FILTRATION degree. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

noncomputable def nativeRelativeReducedData {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) : NativeNilmanifoldData.{u} s := by
  letI := native_relative_terminal_subgroup_normal D d hd
  letI : IsClosed (nativeRelativeTerminalModel D d hd : Set (nativeRelativeSquareData D d hd 1).E) :=
    native_relative_terminal_model_closed D d hd
  let F := (nativeRelativeSquareData D d hd 1).E ⧸ nativeRelativeTerminalModel D d hd
  let Q := (nativeRelativeSquareData D d hd 1).G ⧸ nativeRelativeTerminalSubgroup D d hd
  letI := nativeRelativeReducedChartedSpace D d hd
  letI := native_relative_reduced_lieGroup D d hd
  letI := native_relative_reduced_boundaryless D d hd
  letI := native_relative_reduced_t2Space D d hd
  letI := native_relative_reduced_simplyConnected D d hd
  letI := native_relative_reduced_lattice_discrete D d hd
  letI := native_relative_reduced_lattice_cocompact D d hd
  exact {
    E := F
    H := F
    I := 𝓘(ℝ,F)
    G := Q
    charted := nativeRelativeReducedChartedSpace D d hd
    lie := native_relative_reduced_lieGroup D d hd
    boundaryless := native_relative_reduced_boundaryless D d hd
    rationalModule := Module.compHom F (algebraMap ℚ ℝ)
    step_le := (Group.nilpotencyClass_quotient_le (nativeRelativeTerminalSubgroup D d hd)).trans
      (nativeRelativeSquareData D d hd 1).step_le
    Γ := (nativeRelativeSquareData D d hd 1).Γ.map (QuotientGroup.mk' (nativeRelativeTerminalSubgroup D d hd))
    metric := nativeRelativeReducedMetric D d hd
    metric_quotientMap := native_relative_reduced_metric_quotientMap D d hd }

theorem native_relative_reduced_data_group {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    (nativeRelativeReducedData D d hd).G =
      ((nativeRelativeSquareData D d hd 1).G ⧸ nativeRelativeTerminalSubgroup D d hd) := rfl

theorem native_relative_reduced_data_model {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    (nativeRelativeReducedData D d hd).E =
      ((nativeRelativeSquareData D d hd 1).E ⧸ nativeRelativeTerminalModel D d hd) := rfl

theorem native_relative_reduced_data_lattice {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    letI := native_relative_terminal_subgroup_normal D d hd
    (nativeRelativeReducedData D d hd).Γ = (nativeRelativeSquareData D d hd 1).Γ.map
      (QuotientGroup.mk' (nativeRelativeTerminalSubgroup D d hd)) := rfl

end Hindman168
