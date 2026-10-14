import Hindman168.NativeCentralChildZeroObservable
import Hindman168.CompactLipschitzApproximation

/-! Genuine compact CHILD-metric zero-mode family and one fixed finite
bounded spatial-Lipschitz approximation family, before ALL original F. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_central_child_zero_functionspace_lipschitz {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
    letI := (nativeCentralQuotientData D).metric
    letI : TopologicalSpace ((nativeCentralQuotientData D).G ⧸ (nativeCentralQuotientData D).Γ) :=
      (nativeCentralQuotientData D).metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace ((nativeCentralQuotientData D).G ⧸ (nativeCentralQuotientData D).Γ) :=
      native_nilmanifold_metric_quotient_compact (nativeCentralQuotientData D)
    LipschitzWith 1 (nativeCentralChildZeroObservable D) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  letI := (nativeCentralQuotientData D).metric
  letI : TopologicalSpace ((nativeCentralQuotientData D).G ⧸ (nativeCentralQuotientData D).Γ) :=
    (nativeCentralQuotientData D).metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace ((nativeCentralQuotientData D).G ⧸ (nativeCentralQuotientData D).Γ) :=
    native_nilmanifold_metric_quotient_compact (nativeCentralQuotientData D)
  apply LipschitzWith.mk_one
  intro F G
  simp only [dist_eq_norm]
  rw [← native_central_child_zero_sub]
  exact native_central_child_zero_norm D (F-G)

theorem native_central_child_zero_family_compact {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeCentralQuotientData D).metric
    letI : TopologicalSpace ((nativeCentralQuotientData D).G ⧸ (nativeCentralQuotientData D).Γ) :=
      (nativeCentralQuotientData D).metric.toUniformSpace.toTopologicalSpace
    IsCompact (nativeCentralChildZeroObservable D '' unitLipschitzObservables (D.G ⧸ D.Γ)) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  letI := (nativeCentralQuotientData D).metric
  letI : TopologicalSpace ((nativeCentralQuotientData D).G ⧸ (nativeCentralQuotientData D).Γ) :=
    (nativeCentralQuotientData D).metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace ((nativeCentralQuotientData D).G ⧸ (nativeCentralQuotientData D).Γ) :=
    native_nilmanifold_metric_quotient_compact (nativeCentralQuotientData D)
  exact (unit_lipschitz_observables_compact (D.G ⧸ D.Γ)).image
    (native_central_child_zero_functionspace_lipschitz D).continuous

theorem native_central_child_zero_regular_approximation {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (ε : ℝ) (hε : 0 < ε) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeCentralQuotientData D).metric
    letI : TopologicalSpace ((nativeCentralQuotientData D).G ⧸ (nativeCentralQuotientData D).Γ) :=
      (nativeCentralQuotientData D).metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace ((nativeCentralQuotientData D).G ⧸ (nativeCentralQuotientData D).Γ) :=
      native_nilmanifold_metric_quotient_compact (nativeCentralQuotientData D)
    ∃ B L : ℝ, 0 < B ∧ 0 < L ∧
      ∃ P : Finset C((nativeCentralQuotientData D).G ⧸ (nativeCentralQuotientData D).Γ, ℂ),
        (∀ G ∈ P, (∀ y, ‖G y‖ ≤ B) ∧ LipschitzWith (Real.toNNReal L) G) ∧
        ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ), ∃ G ∈ P, ‖nativeCentralChildZeroObservable D F-G‖ < ε := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeCentralQuotientData D).metric
  letI : TopologicalSpace ((nativeCentralQuotientData D).G ⧸ (nativeCentralQuotientData D).Γ) :=
    (nativeCentralQuotientData D).metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace ((nativeCentralQuotientData D).G ⧸ (nativeCentralQuotientData D).Γ) :=
    native_nilmanifold_metric_quotient_compact (nativeCentralQuotientData D)
  obtain ⟨B,L,hB,hL,P,hP,hClose⟩ := compact_family_bounded_lipschitz_approximation _ _
    (native_central_child_zero_family_compact D) ε hε
  refine ⟨B,L,hB,hL,P,hP,?_⟩
  intro F hF
  exact hClose _ ⟨F,hF,rfl⟩

end Hindman168
