import Hindman168.NativeTerminalReducedPairObservable

/-! Genuine uniform-norm compactness of SAME descended translated
terminal-pair family for compact ORIGINAL translation parameters. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_terminal_reduced_pair_difference_bound {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (k : nativeOriginalTerminalIndex D d → ℤ)
    (g h : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F H : C(D.G ⧸ D.Γ,ℂ),
      ‖nativeTerminalReducedPairObservable D d hd k g F-nativeTerminalReducedPairObservable D d hd k h H‖ ≤
        ‖nativeTerminalRelativePairObservable D d hd k g F-nativeTerminalRelativePairObservable D d hd k h H‖ := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := native_relative_terminal_subgroup_normal D d hd
  intro F H
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro y
  have hs : Function.Surjective (nativeRelativeReductionFactorMap D d hd) :=
    central_subgroup_factor_map_surjective _ _
  obtain ⟨q,rfl⟩ := hs y
  simp only [ContinuousMap.sub_apply,native_terminal_reduced_pair_observable_apply]
  exact (nativeTerminalRelativePairObservable D d hd k g F-nativeTerminalRelativePairObservable D d hd k h H).norm_coe_le_norm q

theorem native_terminal_reduced_pair_observable_continuous {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (k : nativeOriginalTerminalIndex D d → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    Continuous (fun p : D.G × C(D.G ⧸ D.Γ,ℂ) => nativeTerminalReducedPairObservable D d hd k p.1 p.2) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  apply continuous_iff_continuousAt.mpr
  intro p
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := Metric.tendsto_nhds.mp
    ((native_terminal_relative_pair_observable_continuous D d hd k).continuousAt (x := p)) ε hε
  filter_upwards [he] with q hq
  have h := native_terminal_reduced_pair_difference_bound D d hd k q.1 p.1 q.2 p.2
  simp only [← dist_eq_norm] at h
  exact h.trans_lt hq

theorem native_terminal_reduced_pair_family_compact {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (k : nativeOriginalTerminalIndex D d → ℤ)
    (K : Set D.G) (hK : IsCompact K) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    IsCompact ((fun p : D.G × C(D.G ⧸ D.Γ,ℂ) => nativeTerminalReducedPairObservable D d hd k p.1 p.2) ''
      (K ×ˢ unitLipschitzObservables (D.G ⧸ D.Γ))) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  exact (hK.prod (unit_lipschitz_observables_compact (D.G ⧸ D.Γ))).image
    (native_terminal_reduced_pair_observable_continuous D d hd k)

end Hindman168
