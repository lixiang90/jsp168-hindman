import Hindman168.NativeRelativeTerminalSubgroup
import Hindman168.NativeCentralSubspaceQuotientLieGroup
import Hindman168.SubgroupQuotientStructureTransport

/-! ACTUAL original relative group modulo SAME terminal diagonal has
genuine quotient chart/Lie/boundaryless/T2/simply-connected structures. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three
attribute [local instance] nativeCentralSubspaceSubgroup_normal

@[reducible]
noncomputable def nativeRelativeReducedChartedSpace {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    letI : IsClosed (nativeRelativeTerminalModel D d hd : Set (nativeRelativeSquareData D d hd 1).E) :=
      native_relative_terminal_model_closed D d hd
    ChartedSpace ((nativeRelativeSquareData D d hd 1).E ⧸ nativeRelativeTerminalModel D d hd)
      ((nativeRelativeSquareData D d hd 1).G ⧸ nativeRelativeTerminalSubgroup D d hd) := by
  letI : IsClosed (nativeRelativeTerminalModel D d hd : Set (nativeRelativeSquareData D d hd 1).E) :=
    native_relative_terminal_model_closed D d hd
  exact subgroupQuotientChartedSpaceOfEq _ _ (native_relative_terminal_subgroup_central_eq D d hd)
    (nativeCentralSubspaceQuotientChartedSpace (I := (nativeRelativeSquareData D d hd 1).I)
      (nativeRelativeTerminalModel D d hd) (native_relative_terminal_model_le_center D d hd))

theorem native_relative_reduced_lieGroup {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    letI := native_relative_terminal_subgroup_normal D d hd
    letI : IsClosed (nativeRelativeTerminalModel D d hd : Set (nativeRelativeSquareData D d hd 1).E) :=
      native_relative_terminal_model_closed D d hd
    letI := nativeRelativeReducedChartedSpace D d hd
    LieGroup 𝓘(ℝ,(nativeRelativeSquareData D d hd 1).E ⧸ nativeRelativeTerminalModel D d hd) ∞
      ((nativeRelativeSquareData D d hd 1).G ⧸ nativeRelativeTerminalSubgroup D d hd) := by
  letI := native_relative_terminal_subgroup_normal D d hd
  letI : IsClosed (nativeRelativeTerminalModel D d hd : Set (nativeRelativeSquareData D d hd 1).E) :=
    native_relative_terminal_model_closed D d hd
  let c := nativeCentralSubspaceQuotientChartedSpace (I := (nativeRelativeSquareData D d hd 1).I)
    (nativeRelativeTerminalModel D d hd) (native_relative_terminal_model_le_center D d hd)
  letI := c
  exact subgroup_quotient_lieGroup_of_eq _ _ _ (native_relative_terminal_subgroup_central_eq D d hd) c
    (nativeCentralSubspaceQuotient_lieGroup (I := (nativeRelativeSquareData D d hd 1).I)
      (nativeRelativeTerminalModel D d hd) (native_relative_terminal_model_le_center D d hd))

theorem native_relative_reduced_boundaryless {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    letI : IsClosed (nativeRelativeTerminalModel D d hd : Set (nativeRelativeSquareData D d hd 1).E) :=
      native_relative_terminal_model_closed D d hd
    letI := nativeRelativeReducedChartedSpace D d hd
    BoundarylessManifold 𝓘(ℝ,(nativeRelativeSquareData D d hd 1).E ⧸ nativeRelativeTerminalModel D d hd)
      ((nativeRelativeSquareData D d hd 1).G ⧸ nativeRelativeTerminalSubgroup D d hd) := by
  letI : IsClosed (nativeRelativeTerminalModel D d hd : Set (nativeRelativeSquareData D d hd 1).E) :=
    native_relative_terminal_model_closed D d hd
  let c := nativeCentralSubspaceQuotientChartedSpace (I := (nativeRelativeSquareData D d hd 1).I)
    (nativeRelativeTerminalModel D d hd) (native_relative_terminal_model_le_center D d hd)
  letI := c
  letI := nativeCentralSubspaceQuotient_isManifold (I := (nativeRelativeSquareData D d hd 1).I)
    (nativeRelativeTerminalModel D d hd) (native_relative_terminal_model_le_center D d hd)
  have h : BoundarylessManifold 𝓘(ℝ,(nativeRelativeSquareData D d hd 1).E ⧸ nativeRelativeTerminalModel D d hd)
      ((nativeRelativeSquareData D d hd 1).G ⧸ nativeCentralSubspaceSubgroup
        (I := (nativeRelativeSquareData D d hd 1).I) (nativeRelativeTerminalModel D d hd)
        (native_relative_terminal_model_le_center D d hd)) := inferInstance
  exact subgroup_quotient_boundaryless_of_eq _ _ _ (native_relative_terminal_subgroup_central_eq D d hd) c h

theorem native_relative_reduced_t2Space {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    T2Space ((nativeRelativeSquareData D d hd 1).G ⧸ nativeRelativeTerminalSubgroup D d hd) := by
  letI : IsClosed (nativeRelativeTerminalModel D d hd : Set (nativeRelativeSquareData D d hd 1).E) :=
    native_relative_terminal_model_closed D d hd
  exact subgroup_quotient_t2_of_eq _ _ (native_relative_terminal_subgroup_central_eq D d hd)
    (nativeCentralSubspaceQuotient_t2Space (I := (nativeRelativeSquareData D d hd 1).I)
      (nativeRelativeTerminalModel D d hd) (native_relative_terminal_model_le_center D d hd))

theorem native_relative_reduced_simplyConnected {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    SimplyConnectedSpace ((nativeRelativeSquareData D d hd 1).G ⧸ nativeRelativeTerminalSubgroup D d hd) := by
  letI : IsClosed (nativeRelativeTerminalModel D d hd : Set (nativeRelativeSquareData D d hd 1).E) :=
    native_relative_terminal_model_closed D d hd
  exact subgroup_quotient_simplyConnected_of_eq _ _ (native_relative_terminal_subgroup_central_eq D d hd)
    (nativeCentralSubspaceQuotient_simplyConnected (I := (nativeRelativeSquareData D d hd 1).I)
      (nativeRelativeTerminalModel D d hd) (native_relative_terminal_model_le_center D d hd))

end Hindman168
