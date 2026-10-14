import Hindman168.NativeRationalTerminalRelativeMetricObservable
import Hindman168.NativeRationalDegreeRecursion
import Hindman168.NativeRationalTerminalFactorTopology

/-! Actual relative terminal pair descends through the true terminal factor in both specified metrics. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_rational_terminal_relative_metric_subgroup_invariant {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) (g : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeRationalRelativeData D L 1).metric
    letI : TopologicalSpace ((nativeRationalRelativeData D L 1).G ⧸ (nativeRationalRelativeData D L 1).Γ) :=
      (nativeRationalRelativeData D L 1).metric.toUniformSpace.toTopologicalSpace
    ∀ (H : C(D.G ⧸ D.Γ,ℂ))
      (z : nativeRationalTerminalSubgroup (nativeRationalRelativeData D L 1) (nativeRelativeRationalLieFiltration D L))
      (q : (nativeRationalRelativeData D L 1).G ⧸ (nativeRationalRelativeData D L 1).Γ),
      nativeRationalTerminalRelativeMetricObservable D L k g H (z.val • q) =
        nativeRationalTerminalRelativeMetricObservable D L k g H q := by
  intro H z q
  simp only [native_rational_terminal_relative_metric_observable_apply]
  exact native_rational_terminal_relative_pair_subgroup_invariant D L k g H z q

noncomputable def nativeRationalTerminalReducedPairObservable {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (k : nativeRationalTerminalIndex D L → ℤ) (g : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeRationalDegreeReducedData D L).metric
    letI : TopologicalSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
      (nativeRationalDegreeReducedData D L).metric.toUniformSpace.toTopologicalSpace
    letI := (nativeRationalRelativeData D L 1).metric
    letI : TopologicalSpace ((nativeRationalRelativeData D L 1).G ⧸ (nativeRationalRelativeData D L 1).Γ) :=
      (nativeRationalRelativeData D L 1).metric.toUniformSpace.toTopologicalSpace
    C(D.G ⧸ D.Γ,ℂ) → C((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ,ℂ) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRationalDegreeReducedData D L).metric
  letI : TopologicalSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
    (nativeRationalDegreeReducedData D L).metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRationalRelativeData D L 1).metric
  letI : TopologicalSpace ((nativeRationalRelativeData D L 1).G ⧸ (nativeRationalRelativeData D L 1).Γ) :=
    (nativeRationalRelativeData D L 1).metric.toUniformSpace.toTopologicalSpace
  intro H
  exact (native_rational_terminal_factor_metric_openQuotient (nativeRationalRelativeData D L 1) (nativeRelativeRationalLieFiltration D L)).isQuotientMap.lift
    (f := ⟨nativeRationalTerminalFactorMap (nativeRationalRelativeData D L 1) (nativeRelativeRationalLieFiltration D L),(native_rational_terminal_factor_metric_openQuotient (nativeRationalRelativeData D L 1) (nativeRelativeRationalLieFiltration D L)).continuous⟩)
    (nativeRationalTerminalRelativeMetricObservable D L k g H) (by
      intro q r he
      obtain ⟨z,rfl⟩ := (native_rational_terminal_factor_fiber_iff (nativeRationalRelativeData D L 1) (nativeRelativeRationalLieFiltration D L) q r).mp he
      exact (native_rational_terminal_relative_metric_subgroup_invariant D L k g H z q).symm)

theorem native_rational_terminal_reduced_pair_observable_apply {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (k : nativeRationalTerminalIndex D L → ℤ) (g : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeRationalDegreeReducedData D L).metric
    letI : TopologicalSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
      (nativeRationalDegreeReducedData D L).metric.toUniformSpace.toTopologicalSpace
    letI := (nativeRationalRelativeData D L 1).metric
    letI : TopologicalSpace ((nativeRationalRelativeData D L 1).G ⧸ (nativeRationalRelativeData D L 1).Γ) :=
      (nativeRationalRelativeData D L 1).metric.toUniformSpace.toTopologicalSpace
    ∀ (H : C(D.G ⧸ D.Γ,ℂ)) (q : (nativeRationalRelativeData D L 1).G ⧸ (nativeRationalRelativeData D L 1).Γ),
      nativeRationalTerminalReducedPairObservable D L k g H (nativeRationalTerminalFactorMap (nativeRationalRelativeData D L 1) (nativeRelativeRationalLieFiltration D L) q) =
        nativeRationalTerminalRelativeMetricObservable D L k g H q := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRationalDegreeReducedData D L).metric
  letI : TopologicalSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
    (nativeRationalDegreeReducedData D L).metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRationalRelativeData D L 1).metric
  letI : TopologicalSpace ((nativeRationalRelativeData D L 1).G ⧸ (nativeRationalRelativeData D L 1).Γ) :=
    (nativeRationalRelativeData D L 1).metric.toUniformSpace.toTopologicalSpace
  intro H q
  have he := (native_rational_terminal_factor_metric_openQuotient (nativeRationalRelativeData D L 1) (nativeRelativeRationalLieFiltration D L)).isQuotientMap.lift_comp
    (f := ⟨nativeRationalTerminalFactorMap (nativeRationalRelativeData D L 1) (nativeRelativeRationalLieFiltration D L),(native_rational_terminal_factor_metric_openQuotient (nativeRationalRelativeData D L 1) (nativeRelativeRationalLieFiltration D L)).continuous⟩)
    (nativeRationalTerminalRelativeMetricObservable D L k g H) (by
      intro q r he
      obtain ⟨z,rfl⟩ := (native_rational_terminal_factor_fiber_iff (nativeRationalRelativeData D L 1) (nativeRelativeRationalLieFiltration D L) q r).mp he
      exact (native_rational_terminal_relative_metric_subgroup_invariant D L k g H z q).symm)
  exact congrArg (fun K : C((nativeRationalRelativeData D L 1).G ⧸ (nativeRationalRelativeData D L 1).Γ,ℂ) => K q) he

end Hindman168
