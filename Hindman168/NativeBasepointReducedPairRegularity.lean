import Hindman168.NativeBasepointObservable
import Hindman168.NativeTerminalReducedMetricObservable
import Hindman168.CompactLipschitzApproximation

/-! Actual reduced pairs after BOTH original basepoint and linear-shift
translations form a compact family in the actual reduced specified metric.
ONE finite spatial Lipschitz approximant family works for all original inputs. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_basepoint_reduced_pair_continuous {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (k : nativeOriginalTerminalIndex D d → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeRelativeReducedData D d hd).metric
    letI : TopologicalSpace ((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ) :=
      (nativeRelativeReducedData D d hd).metric.toUniformSpace.toTopologicalSpace
    Continuous (fun p : (D.G × D.G) × C(D.G ⧸ D.Γ,ℂ) =>
      nativeTerminalReducedMetricObservable D d hd k p.1.2 (nativeBasepointObservable D p.1.1 p.2)) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  have hBase : Continuous (fun p : (D.G × D.G) × C(D.G ⧸ D.Γ,ℂ) =>
      nativeBasepointObservable D p.1.1 p.2) :=
    (native_basepoint_observable_continuous D).comp (continuous_fst.fst.prodMk continuous_snd)
  have hPair : Continuous (fun p : (D.G × D.G) × C(D.G ⧸ D.Γ,ℂ) =>
      (p.1.2,nativeBasepointObservable D p.1.1 p.2)) := continuous_fst.snd.prodMk hBase
  have hRaw := (native_terminal_reduced_pair_observable_continuous D d hd k).comp hPair
  letI := (nativeRelativeReducedData D d hd).metric
  letI : TopologicalSpace ((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ) :=
    (nativeRelativeReducedData D d hd).metric.toUniformSpace.toTopologicalSpace
  exact (continuous_map_topology_transport_continuous
    ((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ) _ _
    (nativeNilmanifold_metric_topology (nativeRelativeReducedData D d hd))).comp hRaw

theorem native_basepoint_reduced_pair_family_compact {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (k : nativeOriginalTerminalIndex D d → ℤ)
    (K T : Set D.G) (hK : IsCompact K) (hT : IsCompact T) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeRelativeReducedData D d hd).metric
    letI : TopologicalSpace ((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ) :=
      (nativeRelativeReducedData D d hd).metric.toUniformSpace.toTopologicalSpace
    IsCompact ((fun p : (D.G × D.G) × C(D.G ⧸ D.Γ,ℂ) =>
      nativeTerminalReducedMetricObservable D d hd k p.1.2 (nativeBasepointObservable D p.1.1 p.2)) ''
        ((K ×ˢ T) ×ˢ unitLipschitzObservables (D.G ⧸ D.Γ))) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRelativeReducedData D d hd).metric
  letI : TopologicalSpace ((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ) :=
    (nativeRelativeReducedData D d hd).metric.toUniformSpace.toTopologicalSpace
  exact ((hK.prod hT).prod (unit_lipschitz_observables_compact (D.G ⧸ D.Γ))).image
    (native_basepoint_reduced_pair_continuous D d hd k)

theorem native_basepoint_reduced_pair_regular_approximation {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (k : nativeOriginalTerminalIndex D d → ℤ)
    (K T : Set D.G) (hK : IsCompact K) (hT : IsCompact T) (ε : ℝ) (hε : 0 < ε) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeRelativeReducedData D d hd).metric
    letI : TopologicalSpace ((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ) :=
      (nativeRelativeReducedData D d hd).metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace ((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ) :=
      native_nilmanifold_metric_quotient_compact (nativeRelativeReducedData D d hd)
    ∃ B L : ℝ, 0 < B ∧ 0 < L ∧
      ∃ P : Finset C((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ,ℂ),
        (∀ H ∈ P, (∀ y, ‖H y‖ ≤ B) ∧ LipschitzWith (Real.toNNReal L) H) ∧
        ∀ r ∈ K, ∀ t ∈ T, ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
          ∃ H ∈ P, ‖nativeTerminalReducedMetricObservable D d hd k t (nativeBasepointObservable D r F)-H‖ < ε := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRelativeReducedData D d hd).metric
  letI : TopologicalSpace ((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ) :=
    (nativeRelativeReducedData D d hd).metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace ((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ) :=
    native_nilmanifold_metric_quotient_compact (nativeRelativeReducedData D d hd)
  obtain ⟨B,L,hB,hL,P,hP,hClose⟩ := compact_family_bounded_lipschitz_approximation _ _
    (native_basepoint_reduced_pair_family_compact D d hd k K T hK hT) ε hε
  refine ⟨B,L,hB,hL,P,hP,?_⟩
  intro r hr t ht F hF
  exact hClose _ ⟨((r,t),F),⟨⟨hr,ht⟩,hF⟩,rfl⟩

end Hindman168
