import Hindman168.NativeDiagonalPairMetricObservable
import Hindman168.CompactLipschitzApproximation

/-! ONE fixed finite bounded spatial-Lipschitz list approximates ALL actual
original paired observables in actual diagonal native specified metric. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_diagonal_pair_regular_approximation {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (k : nativeNilmanifoldCenterIndex D → ℤ) (ε : ℝ) (hε : 0 < ε) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeDiagonalQuotientData D).metric
    letI : TopologicalSpace ((nativeDiagonalQuotientData D).G ⧸ (nativeDiagonalQuotientData D).Γ) :=
      (nativeDiagonalQuotientData D).metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace ((nativeDiagonalQuotientData D).G ⧸ (nativeDiagonalQuotientData D).Γ) :=
      native_nilmanifold_metric_quotient_compact (nativeDiagonalQuotientData D)
    ∃ B L : ℝ, 0 < B ∧ 0 < L ∧
      ∃ P : Finset C((nativeDiagonalQuotientData D).G ⧸ (nativeDiagonalQuotientData D).Γ, ℂ),
        (∀ G ∈ P, (∀ y, ‖G y‖ ≤ B) ∧ LipschitzWith (Real.toNNReal L) G) ∧
        ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
          ∃ G ∈ P, ‖nativeDiagonalPairMetricObservable D k F-G‖ < ε := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeDiagonalQuotientData D).metric
  letI : TopologicalSpace ((nativeDiagonalQuotientData D).G ⧸ (nativeDiagonalQuotientData D).Γ) :=
    (nativeDiagonalQuotientData D).metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace ((nativeDiagonalQuotientData D).G ⧸ (nativeDiagonalQuotientData D).Γ) :=
    native_nilmanifold_metric_quotient_compact (nativeDiagonalQuotientData D)
  obtain ⟨B,L,hB,hL,P,hP,hClose⟩ := compact_family_bounded_lipschitz_approximation _ _
    (native_diagonal_pair_metric_family_compact D k) ε hε
  refine ⟨B,L,hB,hL,P,hP,?_⟩
  intro F hF
  exact hClose _ ⟨F,hF,rfl⟩

end Hindman168
