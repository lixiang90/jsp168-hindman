import Hindman168.NativeCentralFourierReconstruction

/-! The actual projections send the entire original unit observable family
to compact families. Contraction here is in FUNCTION-SPACE uniform norm. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_central_fourier_projection_sub {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (k : nativeNilmanifoldCenterIndex D → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F G : C(D.G ⧸ D.Γ, ℂ), nativeCentralFourierProjection D k (F-G) =
      nativeCentralFourierProjection D k F - nativeCentralFourierProjection D k G := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F G
  ext q
  change unitTorusKernelEvaluation (UnitAddTorus.mFourier (-k)) (nativeCentralOrbitObservable D (F-G) q) =
    unitTorusKernelEvaluation (UnitAddTorus.mFourier (-k)) (nativeCentralOrbitObservable D F q) -
      unitTorusKernelEvaluation (UnitAddTorus.mFourier (-k)) (nativeCentralOrbitObservable D G q)
  have he : nativeCentralOrbitObservable D (F-G) q =
      nativeCentralOrbitObservable D F q - nativeCentralOrbitObservable D G q := by
    ext a
    rfl
  rw [he, unit_torus_kernel_evaluation_sub]

theorem native_central_fourier_projection_functionspace_lipschitz {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (k : nativeNilmanifoldCenterIndex D → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
    LipschitzWith 1 (nativeCentralFourierProjection D k) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  apply LipschitzWith.mk_one
  intro F G
  simp only [dist_eq_norm]
  rw [← native_central_fourier_projection_sub]
  exact native_central_fourier_projection_norm D k (F-G)

theorem native_central_fourier_projection_family_compact {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (k : nativeNilmanifoldCenterIndex D → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    IsCompact (nativeCentralFourierProjection D k '' unitLipschitzObservables (D.G ⧸ D.Γ)) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  exact (unit_lipschitz_observables_compact (D.G ⧸ D.Γ)).image
    (native_central_fourier_projection_functionspace_lipschitz D k).continuous

end Hindman168
