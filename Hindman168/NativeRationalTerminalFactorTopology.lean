import Hindman168.NativeRationalTerminalProjection
import Hindman168.CentralSubgroupFactorFibers
import Hindman168.CentralSubgroupFactorProbability
import Hindman168.NativeMetricMaskModelTesting

/-! The ACTUAL terminal native image-lattice factor has actual original
fibers/equivariance and is an open quotient in BOTH specified native metrics. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_rational_terminal_subgroup_le_center {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    nativeRationalTerminalSubgroup D L ≤ Subgroup.center D.G :=
  nativeCentralSubspaceSubgroup_le_center _ (native_rational_filtered_terminal_central D L)

theorem native_rational_terminal_factor_surjective {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    Function.Surjective (nativeRationalTerminalFactorMap D L) := by
  letI := native_rational_terminal_subgroup_normal D L
  exact central_subgroup_factor_map_surjective (nativeRationalTerminalSubgroup D L) D.Γ

theorem native_rational_terminal_factor_equivariant {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (g : D.G) (q : D.G ⧸ D.Γ) :
    nativeRationalTerminalFactorMap D L (g • q) =
      nativeRationalTerminalGroupProjection D L g • nativeRationalTerminalFactorMap D L q := by
  letI := native_rational_terminal_subgroup_normal D L
  exact central_subgroup_factor_map_equivariant (nativeRationalTerminalSubgroup D L) D.Γ g q

theorem native_rational_terminal_factor_fiber_iff {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (q r : D.G ⧸ D.Γ) :
    nativeRationalTerminalFactorMap D L q = nativeRationalTerminalFactorMap D L r ↔
      ∃ z : nativeRationalTerminalSubgroup D L, r = (z : D.G) • q := by
  letI := native_rational_terminal_subgroup_normal D L
  exact central_subgroup_factor_fiber_iff (nativeRationalTerminalSubgroup D L) D.Γ
    (native_rational_terminal_subgroup_le_center D L) q r

theorem native_rational_terminal_factor_natural_openQuotient {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    @IsOpenQuotientMap (D.G ⧸ D.Γ)
      ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ)
      (QuotientGroup.instTopologicalSpace D.Γ)
      (QuotientGroup.instTopologicalSpace (nativeRationalTerminalQuotientData D L).Γ)
      (nativeRationalTerminalFactorMap D L) := by
  letI := native_rational_terminal_subgroup_normal D L
  exact central_subgroup_factor_map_openQuotient (nativeRationalTerminalSubgroup D L) D.Γ

theorem native_rational_terminal_factor_metric_openQuotient {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeRationalTerminalQuotientData D L).metric
    letI : TopologicalSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
      (nativeRationalTerminalQuotientData D L).metric.toUniformSpace.toTopologicalSpace
    IsOpenQuotientMap (nativeRationalTerminalFactorMap D L) := by
  exact Eq.mp (congrArg₂
    (fun (t : TopologicalSpace (D.G ⧸ D.Γ))
      (u : TopologicalSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ)) =>
      @IsOpenQuotientMap (D.G ⧸ D.Γ)
        ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) t u
        (nativeRationalTerminalFactorMap D L))
    (nativeNilmanifold_metric_topology D)
    (nativeNilmanifold_metric_topology (nativeRationalTerminalQuotientData D L)))
    (native_rational_terminal_factor_natural_openQuotient D L)

theorem native_rational_terminal_factor_original_metric_openQuotient {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    IsOpenQuotientMap (nativeRationalTerminalFactorMap D L) := by
  exact Eq.mp (congrArg (fun t : TopologicalSpace (D.G ⧸ D.Γ) =>
    @IsOpenQuotientMap (D.G ⧸ D.Γ)
      ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) t inferInstance
      (nativeRationalTerminalFactorMap D L)) (nativeNilmanifold_metric_topology D))
    (native_rational_terminal_factor_natural_openQuotient D L)

end Hindman168
