import Hindman168.NativeRationalTerminalLattice
import Hindman168.NativeCentralSubspaceQuotientLieGroup
import Hindman168.SubgroupQuotientStructureTransport

/-! Actual original native terminal quotient structures/model/image lattice/metric for ANY finite rational Lie filtration. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three
attribute [local instance] nativeCentralSubspaceSubgroup_normal

@[reducible]
noncomputable def nativeRationalTerminalQuotientChartedSpace {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    letI : IsClosed ((F.layer ℓ) : Set D.E) :=
      native_rational_terminal_model_closed D F
    ChartedSpace (D.E ⧸ (F.layer ℓ))
      (D.G ⧸ nativeRationalTerminalSubgroup D F) := by
  letI : IsClosed ((F.layer ℓ) : Set D.E) :=
    native_rational_terminal_model_closed D F
  exact subgroupQuotientChartedSpaceOfEq _ _ (native_rational_terminal_central_subgroup_eq D F)
    (nativeCentralSubspaceQuotientChartedSpace (I := D.I)
      ((F.layer ℓ)) (native_rational_filtered_terminal_central D F))

theorem native_rational_terminal_quotient_lieGroup {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    letI := native_rational_terminal_subgroup_normal D F
    letI : IsClosed ((F.layer ℓ) : Set D.E) :=
      native_rational_terminal_model_closed D F
    letI := nativeRationalTerminalQuotientChartedSpace D F
    LieGroup 𝓘(ℝ,D.E ⧸ (F.layer ℓ)) ∞
      (D.G ⧸ nativeRationalTerminalSubgroup D F) := by
  letI := native_rational_terminal_subgroup_normal D F
  letI : IsClosed ((F.layer ℓ) : Set D.E) :=
    native_rational_terminal_model_closed D F
  let c := nativeCentralSubspaceQuotientChartedSpace (I := D.I)
    ((F.layer ℓ)) (native_rational_filtered_terminal_central D F)
  letI := c
  exact subgroup_quotient_lieGroup_of_eq _ _ _ (native_rational_terminal_central_subgroup_eq D F) c
    (nativeCentralSubspaceQuotient_lieGroup (I := D.I)
      ((F.layer ℓ)) (native_rational_filtered_terminal_central D F))

theorem native_rational_terminal_quotient_boundaryless {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    letI : IsClosed ((F.layer ℓ) : Set D.E) :=
      native_rational_terminal_model_closed D F
    letI := nativeRationalTerminalQuotientChartedSpace D F
    BoundarylessManifold 𝓘(ℝ,D.E ⧸ (F.layer ℓ))
      (D.G ⧸ nativeRationalTerminalSubgroup D F) := by
  letI : IsClosed ((F.layer ℓ) : Set D.E) :=
    native_rational_terminal_model_closed D F
  let c := nativeCentralSubspaceQuotientChartedSpace (I := D.I)
    ((F.layer ℓ)) (native_rational_filtered_terminal_central D F)
  letI := c
  letI := nativeCentralSubspaceQuotient_isManifold (I := D.I)
    ((F.layer ℓ)) (native_rational_filtered_terminal_central D F)
  have h : BoundarylessManifold 𝓘(ℝ,D.E ⧸ (F.layer ℓ))
      (D.G ⧸ nativeCentralSubspaceSubgroup
        (I := D.I) ((F.layer ℓ))
        (native_rational_filtered_terminal_central D F)) := inferInstance
  exact subgroup_quotient_boundaryless_of_eq _ _ _ (native_rational_terminal_central_subgroup_eq D F) c h

theorem native_rational_terminal_quotient_t2Space {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    T2Space (D.G ⧸ nativeRationalTerminalSubgroup D F) := by
  letI : IsClosed ((F.layer ℓ) : Set D.E) :=
    native_rational_terminal_model_closed D F
  exact subgroup_quotient_t2_of_eq _ _ (native_rational_terminal_central_subgroup_eq D F)
    (nativeCentralSubspaceQuotient_t2Space (I := D.I)
      ((F.layer ℓ)) (native_rational_filtered_terminal_central D F))

theorem native_rational_terminal_quotient_simplyConnected {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    SimplyConnectedSpace (D.G ⧸ nativeRationalTerminalSubgroup D F) := by
  letI : IsClosed ((F.layer ℓ) : Set D.E) :=
    native_rational_terminal_model_closed D F
  exact subgroup_quotient_simplyConnected_of_eq _ _ (native_rational_terminal_central_subgroup_eq D F)
    (nativeCentralSubspaceQuotient_simplyConnected (I := D.I)
      ((F.layer ℓ)) (native_rational_filtered_terminal_central D F))

end Hindman168
