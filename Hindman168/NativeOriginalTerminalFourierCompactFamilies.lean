import Hindman168.NativeOriginalTerminalFourierReconstruction

/-! ACTUAL ORIGINAL TERMINAL-LAYER specialization. All action inputs are
proved from original terminal centrality/rationality/lattice coordinates.
 The actual projections send the entire original unit observable family
to compact families. Contraction here is in FUNCTION-SPACE uniform norm. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_original_terminal_fourier_projection_sub {s : ℕ} (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (k : nativeOriginalTerminalIndex D d → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F G : C(D.G ⧸ D.Γ, ℂ), nativeOriginalTerminalFourierProjection D d hd k (F-G) =
      nativeOriginalTerminalFourierProjection D d hd k F - nativeOriginalTerminalFourierProjection D d hd k G := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F G
  ext q
  change unitTorusKernelEvaluation (UnitAddTorus.mFourier (-k)) (nativeOriginalTerminalOrbitObservable D d hd (F-G) q) =
    unitTorusKernelEvaluation (UnitAddTorus.mFourier (-k)) (nativeOriginalTerminalOrbitObservable D d hd F q) -
      unitTorusKernelEvaluation (UnitAddTorus.mFourier (-k)) (nativeOriginalTerminalOrbitObservable D d hd G q)
  have he : nativeOriginalTerminalOrbitObservable D d hd (F-G) q =
      nativeOriginalTerminalOrbitObservable D d hd F q - nativeOriginalTerminalOrbitObservable D d hd G q := by
    ext a
    rfl
  rw [he, unit_torus_kernel_evaluation_sub]

theorem native_original_terminal_fourier_projection_functionspace_lipschitz {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (k : nativeOriginalTerminalIndex D d → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
    LipschitzWith 1 (nativeOriginalTerminalFourierProjection D d hd k) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  apply LipschitzWith.mk_one
  intro F G
  simp only [dist_eq_norm]
  rw [← native_original_terminal_fourier_projection_sub]
  exact native_original_terminal_fourier_projection_norm D d hd k (F-G)

theorem native_original_terminal_fourier_projection_family_compact {s : ℕ} (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (k : nativeOriginalTerminalIndex D d → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    IsCompact (nativeOriginalTerminalFourierProjection D d hd k '' unitLipschitzObservables (D.G ⧸ D.Γ)) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  exact (unit_lipschitz_observables_compact (D.G ⧸ D.Γ)).image
    (native_original_terminal_fourier_projection_functionspace_lipschitz D d hd k).continuous

end Hindman168
