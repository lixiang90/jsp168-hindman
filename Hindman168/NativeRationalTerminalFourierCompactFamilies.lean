import Hindman168.NativeRationalTerminalFourierReconstruction

/-! Actual terminal FourierCompactFamilies for ANY original finite rational Lie filtration.
All original central/rational/lattice/action/canonical-Haar inputs are
PROVED using SAME actual terminal layer and SAME original specified metric. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_rational_terminal_fourier_projection_sub {s ℓ : ℕ} (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F G : C(D.G ⧸ D.Γ, ℂ), nativeRationalTerminalFourierProjection D L k (F-G) =
      nativeRationalTerminalFourierProjection D L k F - nativeRationalTerminalFourierProjection D L k G := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F G
  ext q
  change unitTorusKernelEvaluation (UnitAddTorus.mFourier (-k)) (nativeRationalTerminalOrbitObservable D L (F-G) q) =
    unitTorusKernelEvaluation (UnitAddTorus.mFourier (-k)) (nativeRationalTerminalOrbitObservable D L F q) -
      unitTorusKernelEvaluation (UnitAddTorus.mFourier (-k)) (nativeRationalTerminalOrbitObservable D L G q)
  have he : nativeRationalTerminalOrbitObservable D L (F-G) q =
      nativeRationalTerminalOrbitObservable D L F q - nativeRationalTerminalOrbitObservable D L G q := by
    ext a
    rfl
  rw [he, unit_torus_kernel_evaluation_sub]

theorem native_rational_terminal_fourier_projection_functionspace_lipschitz {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (k : nativeRationalTerminalIndex D L → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
    LipschitzWith 1 (nativeRationalTerminalFourierProjection D L k) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  apply LipschitzWith.mk_one
  intro F G
  simp only [dist_eq_norm]
  rw [← native_rational_terminal_fourier_projection_sub]
  exact native_rational_terminal_fourier_projection_norm D L k (F-G)

theorem native_rational_terminal_fourier_projection_family_compact {s ℓ : ℕ} (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    IsCompact (nativeRationalTerminalFourierProjection D L k '' unitLipschitzObservables (D.G ⧸ D.Γ)) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  exact (unit_lipschitz_observables_compact (D.G ⧸ D.Γ)).image
    (native_rational_terminal_fourier_projection_functionspace_lipschitz D L k).continuous

end Hindman168
