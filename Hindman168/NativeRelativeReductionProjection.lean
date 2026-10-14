import Hindman168.NativeRelativeReducedData
import Hindman168.SubgroupQuotientProjectionTransport
import Hindman168.NativeCentralSubspaceQuotientTangent
import Hindman168.CentralSubgroupFactorMap

/-! ACTUAL original relative-to-terminal quotient group/model maps.
True smoothness and identity derivative retain SAME constructed native chart. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three
attribute [local instance] nativeCentralSubspaceSubgroup_normal

noncomputable def nativeRelativeReductionGroupProjection {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    (nativeRelativeSquareData D d hd 1).G →* (nativeRelativeReducedData D d hd).G := by
  letI := native_relative_terminal_subgroup_normal D d hd
  exact QuotientGroup.mk' (nativeRelativeTerminalSubgroup D d hd)

noncomputable def nativeRelativeReductionModelProjection {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    (nativeRelativeSquareData D d hd 1).E →L[ℝ] (nativeRelativeReducedData D d hd).E := by
  letI : IsClosed (nativeRelativeTerminalModel D d hd : Set (nativeRelativeSquareData D d hd 1).E) :=
    native_relative_terminal_model_closed D d hd
  exact finiteRealQuotientProjection (nativeRelativeTerminalModel D d hd)

noncomputable def nativeRelativeReductionFactorMap {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    ((nativeRelativeSquareData D d hd 1).G ⧸ (nativeRelativeSquareData D d hd 1).Γ) →
      ((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ) := by
  letI := native_relative_terminal_subgroup_normal D d hd
  exact centralSubgroupFactorMap (nativeRelativeTerminalSubgroup D d hd) (nativeRelativeSquareData D d hd 1).Γ

theorem native_relative_reduction_projection_contMDiff {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    ContMDiff (nativeRelativeSquareData D d hd 1).I (nativeRelativeReducedData D d hd).I ∞
      (nativeRelativeReductionGroupProjection D d hd) := by
  letI := native_relative_terminal_subgroup_normal D d hd
  letI : IsClosed (nativeRelativeTerminalModel D d hd : Set (nativeRelativeSquareData D d hd 1).E) :=
    native_relative_terminal_model_closed D d hd
  let c := nativeCentralSubspaceQuotientChartedSpace (I := (nativeRelativeSquareData D d hd 1).I)
    (nativeRelativeTerminalModel D d hd) (native_relative_terminal_model_le_center D d hd)
  letI := c
  exact subgroup_quotient_projection_contMDiff_of_eq (nativeRelativeSquareData D d hd 1).I
    𝓘(ℝ,(nativeRelativeSquareData D d hd 1).E ⧸ nativeRelativeTerminalModel D d hd) _ _
    (native_relative_terminal_subgroup_central_eq D d hd) c
    (nativeCentralSubspaceQuotient_projection_contMDiff (I := (nativeRelativeSquareData D d hd 1).I)
      (nativeRelativeTerminalModel D d hd) (native_relative_terminal_model_le_center D d hd))

theorem native_relative_reduction_projection_mfderiv {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    mfderiv (nativeRelativeSquareData D d hd 1).I (nativeRelativeReducedData D d hd).I
      (nativeRelativeReductionGroupProjection D d hd) 1 = nativeRelativeReductionModelProjection D d hd := by
  letI := native_relative_terminal_subgroup_normal D d hd
  letI : IsClosed (nativeRelativeTerminalModel D d hd : Set (nativeRelativeSquareData D d hd 1).E) :=
    native_relative_terminal_model_closed D d hd
  let c := nativeCentralSubspaceQuotientChartedSpace (I := (nativeRelativeSquareData D d hd 1).I)
    (nativeRelativeTerminalModel D d hd) (native_relative_terminal_model_le_center D d hd)
  letI := c
  exact subgroup_quotient_projection_mfderiv_of_eq (nativeRelativeSquareData D d hd 1).I
    𝓘(ℝ,(nativeRelativeSquareData D d hd 1).E ⧸ nativeRelativeTerminalModel D d hd) _ _
    (native_relative_terminal_subgroup_central_eq D d hd) c 1
    (finiteRealQuotientProjection (nativeRelativeTerminalModel D d hd))
    (nativeCentralSubspaceQuotient_mfderiv_eq_projection (I := (nativeRelativeSquareData D d hd 1).I)
      (nativeRelativeTerminalModel D d hd) (native_relative_terminal_model_le_center D d hd))

end Hindman168
