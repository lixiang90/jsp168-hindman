import Hindman168.NativeRationalTerminalRelativePairTranslation
import Hindman168.NativeMetricMaskModelTesting
import Hindman168.ContinuousMapTopologyTransport

/-! SAME translated terminal pair is in ACTUAL relative native
specified metric. Point values and genuine compact family are preserved. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

noncomputable def nativeRationalTerminalRelativeMetricObservable {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (k : nativeRationalTerminalIndex D L → ℤ) (g : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeRationalRelativeData D L 1).metric
    letI : TopologicalSpace ((nativeRationalRelativeData D L 1).G ⧸ (nativeRationalRelativeData D L 1).Γ) :=
      (nativeRationalRelativeData D L 1).metric.toUniformSpace.toTopologicalSpace
    C(D.G ⧸ D.Γ,ℂ) → C((nativeRationalRelativeData D L 1).G ⧸ (nativeRationalRelativeData D L 1).Γ,ℂ) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRationalRelativeData D L 1).metric
  letI : TopologicalSpace ((nativeRationalRelativeData D L 1).G ⧸ (nativeRationalRelativeData D L 1).Γ) :=
    (nativeRationalRelativeData D L 1).metric.toUniformSpace.toTopologicalSpace
  intro F
  exact continuousMapTopologyTransport
    ((nativeRationalRelativeData D L 1).G ⧸ (nativeRationalRelativeData D L 1).Γ)
    (QuotientGroup.instTopologicalSpace (nativeRationalRelativeData D L 1).Γ)
    (nativeRationalRelativeData D L 1).metric.toUniformSpace.toTopologicalSpace
    (nativeNilmanifold_metric_topology (nativeRationalRelativeData D L 1))
    (nativeRationalTerminalRelativePairObservable D L k g F)

theorem native_rational_terminal_relative_metric_observable_apply {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (k : nativeRationalTerminalIndex D L → ℤ) (g : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ,ℂ)) (q : (nativeRationalRelativeData D L 1).G ⧸ (nativeRationalRelativeData D L 1).Γ),
      nativeRationalTerminalRelativeMetricObservable D L k g F q = nativeRationalTerminalRelativePairObservable D L k g F q := by
  intro F q
  exact continuous_map_topology_transport_apply _ _ _ _ _ q

theorem native_rational_terminal_relative_metric_observable_continuous {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (k : nativeRationalTerminalIndex D L → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeRationalRelativeData D L 1).metric
    letI : TopologicalSpace ((nativeRationalRelativeData D L 1).G ⧸ (nativeRationalRelativeData D L 1).Γ) :=
      (nativeRationalRelativeData D L 1).metric.toUniformSpace.toTopologicalSpace
    Continuous (fun p : D.G × C(D.G ⧸ D.Γ,ℂ) => nativeRationalTerminalRelativeMetricObservable D L k p.1 p.2) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRationalRelativeData D L 1).metric
  letI : TopologicalSpace ((nativeRationalRelativeData D L 1).G ⧸ (nativeRationalRelativeData D L 1).Γ) :=
    (nativeRationalRelativeData D L 1).metric.toUniformSpace.toTopologicalSpace
  exact (continuous_map_topology_transport_continuous
    ((nativeRationalRelativeData D L 1).G ⧸ (nativeRationalRelativeData D L 1).Γ) _ _
    (nativeNilmanifold_metric_topology (nativeRationalRelativeData D L 1))).comp
      (native_rational_terminal_relative_pair_observable_continuous D L k)

theorem native_rational_terminal_relative_metric_family_compact {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (k : nativeRationalTerminalIndex D L → ℤ)
    (K : Set D.G) (hK : IsCompact K) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeRationalRelativeData D L 1).metric
    letI : TopologicalSpace ((nativeRationalRelativeData D L 1).G ⧸ (nativeRationalRelativeData D L 1).Γ) :=
      (nativeRationalRelativeData D L 1).metric.toUniformSpace.toTopologicalSpace
    IsCompact ((fun p : D.G × C(D.G ⧸ D.Γ,ℂ) => nativeRationalTerminalRelativeMetricObservable D L k p.1 p.2) ''
      (K ×ˢ unitLipschitzObservables (D.G ⧸ D.Γ))) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRationalRelativeData D L 1).metric
  letI : TopologicalSpace ((nativeRationalRelativeData D L 1).G ⧸ (nativeRationalRelativeData D L 1).Γ) :=
    (nativeRationalRelativeData D L 1).metric.toUniformSpace.toTopologicalSpace
  exact (hK.prod (unit_lipschitz_observables_compact (D.G ⧸ D.Γ))).image
    (native_rational_terminal_relative_metric_observable_continuous D L k)

end Hindman168
