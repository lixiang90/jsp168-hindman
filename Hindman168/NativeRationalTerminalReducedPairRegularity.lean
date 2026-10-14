import Hindman168.NativeRationalTerminalReducedPairCompact
import Hindman168.CompactLipschitzApproximation

/-! ONE FIXED finite ACTUAL target-metric spatial Lipschitz approximant
family works for ALL original unit inputs and compact translation parameters. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_rational_terminal_reduced_pair_regular_approximation {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (k : nativeRationalTerminalIndex D L → ℤ)
    (K : Set D.G) (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeRationalDegreeReducedData D L).metric
    letI : TopologicalSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
      (nativeRationalDegreeReducedData D L).metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
      native_nilmanifold_metric_quotient_compact (nativeRationalDegreeReducedData D L)
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧
      ∃ P : Finset C((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ,ℂ),
        (∀ H ∈ P, (∀ y, ‖H y‖ ≤ B) ∧ LipschitzWith (Real.toNNReal C) H) ∧
        ∀ g ∈ K, ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
          ∃ H ∈ P, ‖nativeRationalTerminalReducedPairObservable D L k g F-H‖ < ε := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRationalDegreeReducedData D L).metric
  letI : TopologicalSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
    (nativeRationalDegreeReducedData D L).metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
    native_nilmanifold_metric_quotient_compact (nativeRationalDegreeReducedData D L)
  obtain ⟨B,C,hB,hC,P,hP,hClose⟩ := compact_family_bounded_lipschitz_approximation _ _
    (native_rational_terminal_reduced_pair_family_compact D L k K hK) ε hε
  refine ⟨B,C,hB,hC,P,hP,?_⟩
  intro g hg F hF
  exact hClose _ ⟨(g,F),⟨hg,hF⟩,rfl⟩

end Hindman168
