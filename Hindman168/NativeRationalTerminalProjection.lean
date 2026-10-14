import Hindman168.NativeRationalTerminalQuotientData
import Hindman168.SubgroupQuotientProjectionTransport
import Hindman168.NativeCentralSubspaceQuotientTangent
import Hindman168.CentralSubgroupFactorMap

/-! Actual original native terminal quotient projection, identity differential and Exp/Log/rational span transport. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three
attribute [local instance] nativeCentralSubspaceSubgroup_normal

noncomputable def nativeRationalTerminalGroupProjection {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    D.G →* (nativeRationalTerminalQuotientData D F).G := by
  letI := native_rational_terminal_subgroup_normal D F
  exact QuotientGroup.mk' (nativeRationalTerminalSubgroup D F)

noncomputable def nativeRationalTerminalModelProjection {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    D.E →L[ℝ] (nativeRationalTerminalQuotientData D F).E := by
  letI : IsClosed ((F.layer ℓ) : Set D.E) :=
    native_rational_terminal_model_closed D F
  exact finiteRealQuotientProjection ((F.layer ℓ))

noncomputable def nativeRationalTerminalFactorMap {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    (D.G ⧸ D.Γ) →
      ((nativeRationalTerminalQuotientData D F).G ⧸ (nativeRationalTerminalQuotientData D F).Γ) := by
  letI := native_rational_terminal_subgroup_normal D F
  exact centralSubgroupFactorMap (nativeRationalTerminalSubgroup D F) D.Γ

theorem native_rational_terminal_projection_contMDiff {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    ContMDiff D.I (nativeRationalTerminalQuotientData D F).I ∞
      (nativeRationalTerminalGroupProjection D F) := by
  letI := native_rational_terminal_subgroup_normal D F
  letI : IsClosed ((F.layer ℓ) : Set D.E) :=
    native_rational_terminal_model_closed D F
  let c := nativeCentralSubspaceQuotientChartedSpace (I := D.I)
    ((F.layer ℓ)) (native_rational_filtered_terminal_central D F)
  letI := c
  exact subgroup_quotient_projection_contMDiff_of_eq D.I
    𝓘(ℝ,D.E ⧸ (F.layer ℓ)) _ _
    (native_rational_terminal_central_subgroup_eq D F) c
    (nativeCentralSubspaceQuotient_projection_contMDiff (I := D.I)
      ((F.layer ℓ)) (native_rational_filtered_terminal_central D F))

theorem native_rational_terminal_projection_mfderiv {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    mfderiv D.I (nativeRationalTerminalQuotientData D F).I
      (nativeRationalTerminalGroupProjection D F) 1 = nativeRationalTerminalModelProjection D F := by
  letI := native_rational_terminal_subgroup_normal D F
  letI : IsClosed ((F.layer ℓ) : Set D.E) :=
    native_rational_terminal_model_closed D F
  let c := nativeCentralSubspaceQuotientChartedSpace (I := D.I)
    ((F.layer ℓ)) (native_rational_filtered_terminal_central D F)
  letI := c
  exact subgroup_quotient_projection_mfderiv_of_eq D.I
    𝓘(ℝ,D.E ⧸ (F.layer ℓ)) _ _
    (native_rational_terminal_central_subgroup_eq D F) c 1
    (finiteRealQuotientProjection ((F.layer ℓ)))
    (nativeCentralSubspaceQuotient_mfderiv_eq_projection (I := D.I)
      ((F.layer ℓ)) (native_rational_filtered_terminal_central D F))

end Hindman168
