import Hindman168.UnitTorusFourierKernelEvaluation
import Hindman168.NativeRationalTerminalFourierProjection

/-! Actual terminal FourierReconstruction for ANY original finite rational Lie filtration.
All original central/rational/lattice/action/canonical-Haar inputs are
PROVED using SAME actual terminal layer and SAME original specified metric. -/

namespace Hindman168
open scoped Manifold ContDiff Classical
universe u

theorem native_rational_terminal_unit_orbit_norm {s ℓ : ℕ} (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ), ∀ q : D.G ⧸ D.Γ,
      ‖nativeRationalTerminalOrbitObservable D L F q‖ ≤ 1 := by
  intro F hF q
  apply (ContinuousMap.norm_le _ zero_le_one).mpr
  intro a
  exact hF.2 (nativeRationalTerminalAction D L a q)

theorem native_rational_terminal_fourier_reconstruction {s ℓ : ℕ} (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (ε : ℝ) (hε : 0 < ε) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
    ∃ c : (nativeRationalTerminalIndex D L → ℤ) →₀ ℂ,
      ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
        ‖F - c.sum (fun k a => a • nativeRationalTerminalFourierProjection D L (-k) F)‖ < ε := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  let H := (fun p : C(D.G ⧸ D.Γ, ℂ) × (D.G ⧸ D.Γ) => nativeRationalTerminalOrbitObservable D L p.1 p.2) ''
    (unitLipschitzObservables (D.G ⧸ D.Γ) ×ˢ Set.univ)
  have hbound : ∀ G ∈ H, ‖G‖ ≤ 1 := by
    rintro G ⟨⟨F,q⟩, ⟨hF, _⟩, rfl⟩
    exact native_rational_terminal_unit_orbit_norm D L F hF q
  obtain ⟨c, hc⟩ := compact_torus_fourier_kernel_reconstruction H
    (native_rational_terminal_unit_orbit_family_compact D L) hbound (ε/2) (by positivity)
  refine ⟨c, ?_⟩
  intro F hF
  have hpoint : ∀ q : D.G ⧸ D.Γ,
      ‖(F-c.sum (fun k a => a • nativeRationalTerminalFourierProjection D L (-k) F)) q‖ < ε/2 := by
    intro q
    have h := hc (nativeRationalTerminalOrbitObservable D L F q) ⟨(F,q), ⟨hF, Set.mem_univ q⟩, rfl⟩
    simp only [native_rational_terminal_orbit_observable_apply, native_rational_terminal_action_zero] at h
    simpa only [Finsupp.sum, ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul, ContinuousMap.sub_apply,
      native_rational_terminal_fourier_projection_apply, neg_neg] using h
  apply lt_of_le_of_lt ((ContinuousMap.norm_le _ (by positivity : 0 ≤ ε/2)).mpr
    (fun q => (hpoint q).le))
  linarith only [hε]

end Hindman168
