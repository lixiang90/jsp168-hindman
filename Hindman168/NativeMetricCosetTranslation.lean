import Hindman168.NativeNilmanifoldProbabilityTesting

/-! Genuine joint continuity of ORIGINAL group translations in the
ACTUAL specified coset metric. No spatial Lipschitz bound is asserted. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_metric_coset_action_continuous {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    Continuous (fun p : D.G × (D.G ⧸ D.Γ) => p.1 • p.2) := by
  have h : Continuous (fun p : D.G × (D.G ⧸ D.Γ) => p.1 • p.2) := continuous_smul
  exact Eq.mp (congrArg (fun t : TopologicalSpace (D.G ⧸ D.Γ) =>
    @Continuous (D.G × (D.G ⧸ D.Γ)) (D.G ⧸ D.Γ)
      (@instTopologicalSpaceProd _ _ D.groupTopology t) t (fun p => p.1 • p.2))
    (nativeNilmanifold_metric_topology D)) h

noncomputable def nativeMetricCosetTranslation {s : ℕ} (D : NativeNilmanifoldData.{u} s) (g : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    C(D.G ⧸ D.Γ,D.G ⧸ D.Γ) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  exact ⟨fun q => g • q,(native_metric_coset_action_continuous D).comp (continuous_const.prodMk continuous_id)⟩

theorem native_metric_coset_translation_apply {s : ℕ} (D : NativeNilmanifoldData.{u} s) (g : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ q : D.G ⧸ D.Γ, nativeMetricCosetTranslation D g q = g • q := by intro q; rfl

end Hindman168
