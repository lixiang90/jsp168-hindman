import Hindman168.NativeRationalTerminalLattice
import Hindman168.NilNaturalCosetMetric

/-! Actual original native terminal quotient structures/model/image lattice/metric for ANY finite rational Lie filtration. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

@[reducible]
noncomputable def nativeRationalTerminalQuotientMetric {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    letI := native_rational_terminal_subgroup_normal D F
    MetricSpace ((D.G ⧸ nativeRationalTerminalSubgroup D F) ⧸
      D.Γ.map (QuotientGroup.mk' (nativeRationalTerminalSubgroup D F))) := by
  letI := native_rational_terminal_subgroup_normal D F
  letI : SecondCountableTopology D.G :=
    (nativeLieGlobalExponentialHomeomorph (I := D.I)
      (G := D.G)).symm.secondCountableTopology
  letI : IsClosed (nativeRationalTerminalSubgroup D F : Set D.G) :=
    native_rational_terminal_subgroup_closed D F
  letI := native_rational_terminal_image_lattice_discrete D F
  letI := native_rational_terminal_image_lattice_cocompact D F
  letI := native_rational_terminal_image_lattice_closed D F
  exact naturalCompactCosetMetric (D.Γ.map
    (QuotientGroup.mk' (nativeRationalTerminalSubgroup D F)))

theorem native_rational_terminal_quotient_metric_topology {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    letI := native_rational_terminal_subgroup_normal D F
    (nativeRationalTerminalQuotientMetric D F).toUniformSpace.toTopologicalSpace =
      QuotientGroup.instTopologicalSpace (D.Γ.map
        (QuotientGroup.mk' (nativeRationalTerminalSubgroup D F))) := by
  letI := native_rational_terminal_subgroup_normal D F
  letI : SecondCountableTopology D.G :=
    (nativeLieGlobalExponentialHomeomorph (I := D.I)
      (G := D.G)).symm.secondCountableTopology
  letI : IsClosed (nativeRationalTerminalSubgroup D F : Set D.G) :=
    native_rational_terminal_subgroup_closed D F
  letI := native_rational_terminal_image_lattice_discrete D F
  letI := native_rational_terminal_image_lattice_cocompact D F
  letI := native_rational_terminal_image_lattice_closed D F
  exact naturalCompactCosetMetric_topology (D.Γ.map
    (QuotientGroup.mk' (nativeRationalTerminalSubgroup D F)))

theorem native_rational_terminal_quotient_metric_quotientMap {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    letI := native_rational_terminal_subgroup_normal D F
    @IsOpenQuotientMap (D.G ⧸ nativeRationalTerminalSubgroup D F)
      ((D.G ⧸ nativeRationalTerminalSubgroup D F) ⧸
        D.Γ.map (QuotientGroup.mk' (nativeRationalTerminalSubgroup D F)))
      inferInstance (nativeRationalTerminalQuotientMetric D F).toUniformSpace.toTopologicalSpace (↑) := by
  letI := native_rational_terminal_subgroup_normal D F
  rw [native_rational_terminal_quotient_metric_topology]
  exact QuotientGroup.isOpenQuotientMap_mk

end Hindman168
