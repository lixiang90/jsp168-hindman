import Hindman168.NativeTerminalReducedPairCompact
import Hindman168.ContinuousMapTopologyTransport

/-! SAME descended translated terminal pair is in ACTUAL reduced native
specified metric. Point values and genuine compact family are preserved. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

noncomputable def nativeTerminalReducedMetricObservable {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (k : nativeOriginalTerminalIndex D d → ℤ) (g : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeRelativeReducedData D d hd).metric
    letI : TopologicalSpace ((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ) :=
      (nativeRelativeReducedData D d hd).metric.toUniformSpace.toTopologicalSpace
    C(D.G ⧸ D.Γ,ℂ) → C((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ,ℂ) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRelativeReducedData D d hd).metric
  letI : TopologicalSpace ((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ) :=
    (nativeRelativeReducedData D d hd).metric.toUniformSpace.toTopologicalSpace
  intro F
  exact continuousMapTopologyTransport
    ((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ)
    (QuotientGroup.instTopologicalSpace (nativeRelativeReducedData D d hd).Γ)
    (nativeRelativeReducedData D d hd).metric.toUniformSpace.toTopologicalSpace
    (nativeNilmanifold_metric_topology (nativeRelativeReducedData D d hd))
    (nativeTerminalReducedPairObservable D d hd k g F)

theorem native_terminal_reduced_metric_observable_apply {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (k : nativeOriginalTerminalIndex D d → ℤ) (g : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ,ℂ)) (q : (nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ),
      nativeTerminalReducedMetricObservable D d hd k g F q = nativeTerminalReducedPairObservable D d hd k g F q := by
  intro F q
  exact continuous_map_topology_transport_apply _ _ _ _ _ q

theorem native_terminal_reduced_metric_observable_continuous {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (k : nativeOriginalTerminalIndex D d → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeRelativeReducedData D d hd).metric
    letI : TopologicalSpace ((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ) :=
      (nativeRelativeReducedData D d hd).metric.toUniformSpace.toTopologicalSpace
    Continuous (fun p : D.G × C(D.G ⧸ D.Γ,ℂ) => nativeTerminalReducedMetricObservable D d hd k p.1 p.2) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRelativeReducedData D d hd).metric
  letI : TopologicalSpace ((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ) :=
    (nativeRelativeReducedData D d hd).metric.toUniformSpace.toTopologicalSpace
  exact (continuous_map_topology_transport_continuous
    ((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ) _ _
    (nativeNilmanifold_metric_topology (nativeRelativeReducedData D d hd))).comp
      (native_terminal_reduced_pair_observable_continuous D d hd k)

theorem native_terminal_reduced_metric_family_compact {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (k : nativeOriginalTerminalIndex D d → ℤ)
    (K : Set D.G) (hK : IsCompact K) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeRelativeReducedData D d hd).metric
    letI : TopologicalSpace ((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ) :=
      (nativeRelativeReducedData D d hd).metric.toUniformSpace.toTopologicalSpace
    IsCompact ((fun p : D.G × C(D.G ⧸ D.Γ,ℂ) => nativeTerminalReducedMetricObservable D d hd k p.1 p.2) ''
      (K ×ˢ unitLipschitzObservables (D.G ⧸ D.Γ))) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRelativeReducedData D d hd).metric
  letI : TopologicalSpace ((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ) :=
    (nativeRelativeReducedData D d hd).metric.toUniformSpace.toTopologicalSpace
  exact (hK.prod (unit_lipschitz_observables_compact (D.G ⧸ D.Γ))).image
    (native_terminal_reduced_metric_observable_continuous D d hd k)

end Hindman168
