import Hindman168.NativeRationalTerminalReducedPairObservable

/-! Genuine uniform-norm compactness of SAME descended translated
terminal-pair family for compact ORIGINAL translation parameters. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_rational_terminal_reduced_pair_difference_bound {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (k : nativeRationalTerminalIndex D L → ℤ)
    (g h : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeRationalDegreeReducedData D L).metric
    letI : TopologicalSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
      (nativeRationalDegreeReducedData D L).metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
      native_nilmanifold_metric_quotient_compact (nativeRationalDegreeReducedData D L)
    ∀ F H : C(D.G ⧸ D.Γ,ℂ),
      ‖nativeRationalTerminalReducedPairObservable D L k g F-nativeRationalTerminalReducedPairObservable D L k h H‖ ≤
        ‖nativeRationalTerminalRelativePairObservable D L k g F-nativeRationalTerminalRelativePairObservable D L k h H‖ := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRationalDegreeReducedData D L).metric
  letI : TopologicalSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
    (nativeRationalDegreeReducedData D L).metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
    native_nilmanifold_metric_quotient_compact (nativeRationalDegreeReducedData D L)
  intro F H
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro y
  have hs : Function.Surjective (nativeRationalTerminalFactorMap (nativeRationalRelativeData D L 1) (nativeRelativeRationalLieFiltration D L)) :=
    native_rational_terminal_factor_surjective (nativeRationalRelativeData D L 1) (nativeRelativeRationalLieFiltration D L)
  obtain ⟨q,rfl⟩ := hs y
  simp only [ContinuousMap.sub_apply,native_rational_terminal_reduced_pair_observable_apply,
    native_rational_terminal_relative_metric_observable_apply]
  exact (nativeRationalTerminalRelativePairObservable D L k g F-nativeRationalTerminalRelativePairObservable D L k h H).norm_coe_le_norm q

theorem native_rational_terminal_reduced_pair_observable_continuous {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (k : nativeRationalTerminalIndex D L → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeRationalDegreeReducedData D L).metric
    letI : TopologicalSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
      (nativeRationalDegreeReducedData D L).metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
      native_nilmanifold_metric_quotient_compact (nativeRationalDegreeReducedData D L)
    Continuous (fun p : D.G × C(D.G ⧸ D.Γ,ℂ) => nativeRationalTerminalReducedPairObservable D L k p.1 p.2) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRationalDegreeReducedData D L).metric
  letI : TopologicalSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
    (nativeRationalDegreeReducedData D L).metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
    native_nilmanifold_metric_quotient_compact (nativeRationalDegreeReducedData D L)
  apply continuous_iff_continuousAt.mpr
  intro p
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := Metric.tendsto_nhds.mp
    ((native_rational_terminal_relative_pair_observable_continuous D L k).continuousAt (x := p)) ε hε
  filter_upwards [he] with q hq
  have h := native_rational_terminal_reduced_pair_difference_bound D L k q.1 p.1 q.2 p.2
  simp only [← dist_eq_norm] at h
  exact h.trans_lt hq

theorem native_rational_terminal_reduced_pair_family_compact {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (k : nativeRationalTerminalIndex D L → ℤ)
    (K : Set D.G) (hK : IsCompact K) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeRationalDegreeReducedData D L).metric
    letI : TopologicalSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
      (nativeRationalDegreeReducedData D L).metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
      native_nilmanifold_metric_quotient_compact (nativeRationalDegreeReducedData D L)
    IsCompact ((fun p : D.G × C(D.G ⧸ D.Γ,ℂ) => nativeRationalTerminalReducedPairObservable D L k p.1 p.2) ''
      (K ×ˢ unitLipschitzObservables (D.G ⧸ D.Γ))) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRationalDegreeReducedData D L).metric
  letI : TopologicalSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
    (nativeRationalDegreeReducedData D L).metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
    native_nilmanifold_metric_quotient_compact (nativeRationalDegreeReducedData D L)
  exact (hK.prod (unit_lipschitz_observables_compact (D.G ⧸ D.Γ))).image
    (native_rational_terminal_reduced_pair_observable_continuous D L k)

end Hindman168
