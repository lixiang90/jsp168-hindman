import Hindman168.UnitTorusFourierKernelEvaluation
import Hindman168.NativeOriginalTerminalFourierProjection

/-! ACTUAL ORIGINAL TERMINAL-LAYER specialization. All action inputs are
proved from original terminal centrality/rationality/lattice coordinates.
The fixed stretch and ACTUAL terminal torus precede every observable.
 A single finite sum of ACTUAL vertical projections reconstructs every
original unit Lipschitz observable uniformly on the original nilmanifold. -/

namespace Hindman168
open scoped Manifold ContDiff Classical
universe u

theorem native_original_terminal_unit_orbit_norm {s : ℕ} (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ), ∀ q : D.G ⧸ D.Γ,
      ‖nativeOriginalTerminalOrbitObservable D d hd F q‖ ≤ 1 := by
  intro F hF q
  apply (ContinuousMap.norm_le _ zero_le_one).mpr
  intro a
  exact hF.2 (nativeOriginalTerminalAction D d hd a q)

theorem native_original_terminal_fourier_reconstruction {s : ℕ} (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (ε : ℝ) (hε : 0 < ε) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
    ∃ c : (nativeOriginalTerminalIndex D d → ℤ) →₀ ℂ,
      ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
        ‖F - c.sum (fun k a => a • nativeOriginalTerminalFourierProjection D d hd (-k) F)‖ < ε := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  let H := (fun p : C(D.G ⧸ D.Γ, ℂ) × (D.G ⧸ D.Γ) => nativeOriginalTerminalOrbitObservable D d hd p.1 p.2) ''
    (unitLipschitzObservables (D.G ⧸ D.Γ) ×ˢ Set.univ)
  have hbound : ∀ G ∈ H, ‖G‖ ≤ 1 := by
    rintro G ⟨⟨F,q⟩, ⟨hF, _⟩, rfl⟩
    exact native_original_terminal_unit_orbit_norm D d hd F hF q
  obtain ⟨c, hc⟩ := compact_torus_fourier_kernel_reconstruction H
    (native_original_terminal_unit_orbit_family_compact D d hd) hbound (ε/2) (by positivity)
  refine ⟨c, ?_⟩
  intro F hF
  have hpoint : ∀ q : D.G ⧸ D.Γ,
      ‖(F-c.sum (fun k a => a • nativeOriginalTerminalFourierProjection D d hd (-k) F)) q‖ < ε/2 := by
    intro q
    have h := hc (nativeOriginalTerminalOrbitObservable D d hd F q) ⟨(F,q), ⟨hF, Set.mem_univ q⟩, rfl⟩
    simp only [native_original_terminal_orbit_observable_apply, native_original_terminal_action_zero] at h
    simpa only [Finsupp.sum, ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul, ContinuousMap.sub_apply,
      native_original_terminal_fourier_projection_apply, neg_neg] using h
  apply lt_of_le_of_lt ((ContinuousMap.norm_le _ (by positivity : 0 ≤ ε/2)).mpr
    (fun q => (hpoint q).le))
  linarith only [hε]

end Hindman168
