import Hindman168.NativeTerminalReducedMetricObservable
import Hindman168.CompactLipschitzApproximation

/-! ONE FIXED finite ACTUAL target-metric spatial Lipschitz approximant
family works for ALL original unit inputs and compact translation parameters. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_terminal_reduced_pair_regular_approximation {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (k : nativeOriginalTerminalIndex D d → ℤ)
    (K : Set D.G) (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
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
        ∀ g ∈ K, ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
          ∃ H ∈ P, ‖nativeTerminalReducedMetricObservable D d hd k g F-H‖ < ε := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRelativeReducedData D d hd).metric
  letI : TopologicalSpace ((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ) :=
    (nativeRelativeReducedData D d hd).metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace ((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ) :=
    native_nilmanifold_metric_quotient_compact (nativeRelativeReducedData D d hd)
  obtain ⟨B,L,hB,hL,P,hP,hClose⟩ := compact_family_bounded_lipschitz_approximation _ _
    (native_terminal_reduced_metric_family_compact D d hd k K hK) ε hε
  refine ⟨B,L,hB,hL,P,hP,?_⟩
  intro g hg F hF
  exact hClose _ ⟨(g,F),⟨hg,hF⟩,rfl⟩

end Hindman168
