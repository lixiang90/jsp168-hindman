import Hindman168.NativeCentralZeroObservable

/-! Actual compact descended zero-mode families in uniform function norm. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_central_zero_observable_sub {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F G : C(D.G ⧸ D.Γ, ℂ), nativeCentralZeroObservable D (F-G) =
      nativeCentralZeroObservable D F - nativeCentralZeroObservable D G := by
  intro F G
  ext y
  obtain ⟨q, rfl⟩ := central_factor_coset_map_surjective D.Γ y
  simp only [native_central_zero_observable_apply, ContinuousMap.sub_apply,
    native_central_fourier_projection_sub]

theorem native_central_zero_functionspace_lipschitz {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
    letI : CompactSpace (nativeCentralFactorSpace D) := native_central_factor_compact D
    LipschitzWith 1 (nativeCentralZeroObservable D) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  letI : CompactSpace (nativeCentralFactorSpace D) := native_central_factor_compact D
  apply LipschitzWith.mk_one
  intro F G
  simp only [dist_eq_norm]
  rw [← native_central_zero_observable_sub]
  exact native_central_zero_observable_norm D (F-G)

theorem native_central_zero_observable_family_compact {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    IsCompact (nativeCentralZeroObservable D '' unitLipschitzObservables (D.G ⧸ D.Γ)) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  letI : CompactSpace (nativeCentralFactorSpace D) := native_central_factor_compact D
  exact (unit_lipschitz_observables_compact (D.G ⧸ D.Γ)).image
    (native_central_zero_functionspace_lipschitz D).continuous

end Hindman168
