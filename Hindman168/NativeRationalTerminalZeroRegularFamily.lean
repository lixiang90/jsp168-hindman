import Hindman168.NativeRationalTerminalZeroSub
import Hindman168.CompactLipschitzApproximation

/-! TRUE zero-mode NativeRationalTerminalZeroRegularFamily on ACTUAL original terminal quotient.
All canonical Haar, SAME image samples and specified-metric inputs are PROVED.
Finite families and positive bounds precede ALL original source observations. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_rational_terminal_zero_functionspace_lipschitz {s ℓ : ℕ} (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
    letI := (nativeRationalTerminalQuotientData D L).metric
    letI : TopologicalSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
      (nativeRationalTerminalQuotientData D L).metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
      native_nilmanifold_metric_quotient_compact (nativeRationalTerminalQuotientData D L)
    LipschitzWith 1 (nativeRationalTerminalZeroObservable D L) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  letI := (nativeRationalTerminalQuotientData D L).metric
  letI : TopologicalSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
    (nativeRationalTerminalQuotientData D L).metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
    native_nilmanifold_metric_quotient_compact (nativeRationalTerminalQuotientData D L)
  apply LipschitzWith.mk_one
  intro F G
  simp only [dist_eq_norm]
  rw [← native_rational_terminal_zero_observable_sub]
  exact native_rational_terminal_zero_observable_norm D L (F-G)

theorem native_rational_terminal_zero_family_compact {s ℓ : ℕ} (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeRationalTerminalQuotientData D L).metric
    letI : TopologicalSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
      (nativeRationalTerminalQuotientData D L).metric.toUniformSpace.toTopologicalSpace
    IsCompact (nativeRationalTerminalZeroObservable D L '' unitLipschitzObservables (D.G ⧸ D.Γ)) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  letI := (nativeRationalTerminalQuotientData D L).metric
  letI : TopologicalSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
    (nativeRationalTerminalQuotientData D L).metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
    native_nilmanifold_metric_quotient_compact (nativeRationalTerminalQuotientData D L)
  exact (unit_lipschitz_observables_compact (D.G ⧸ D.Γ)).image
    (native_rational_terminal_zero_functionspace_lipschitz D L).continuous

theorem native_rational_terminal_zero_regular_approximation {s ℓ : ℕ} (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (ε : ℝ) (hε : 0 < ε) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeRationalTerminalQuotientData D L).metric
    letI : TopologicalSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
      (nativeRationalTerminalQuotientData D L).metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
      native_nilmanifold_metric_quotient_compact (nativeRationalTerminalQuotientData D L)
    ∃ B B_L : ℝ, 0 < B ∧ 0 < B_L ∧
      ∃ P : Finset C((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ, ℂ),
        (∀ G ∈ P, (∀ y, ‖G y‖ ≤ B) ∧ LipschitzWith (Real.toNNReal B_L) G) ∧
        ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ), ∃ G ∈ P, ‖nativeRationalTerminalZeroObservable D L F-G‖ < ε := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRationalTerminalQuotientData D L).metric
  letI : TopologicalSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
    (nativeRationalTerminalQuotientData D L).metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
    native_nilmanifold_metric_quotient_compact (nativeRationalTerminalQuotientData D L)
  obtain ⟨B,B_L,hB,hL,P,hP,hClose⟩ := compact_family_bounded_lipschitz_approximation _ _
    (native_rational_terminal_zero_family_compact D L) ε hε
  refine ⟨B,B_L,hB,hL,P,hP,?_⟩
  intro F hF
  exact hClose _ ⟨F,hF,rfl⟩

end Hindman168
