import Hindman168.UnitTorusFourierKernelEvaluation
import Hindman168.NativeCentralFourierProjection

/-! A single finite sum of ACTUAL vertical projections reconstructs every
original unit Lipschitz observable uniformly on the original nilmanifold. -/

namespace Hindman168
open scoped Manifold ContDiff Classical
universe u

theorem native_central_unit_orbit_norm {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ), ∀ q : D.G ⧸ D.Γ,
      ‖nativeCentralOrbitObservable D F q‖ ≤ 1 := by
  intro F hF q
  apply (ContinuousMap.norm_le _ zero_le_one).mpr
  intro a
  exact hF.2 (nativeNilmanifoldCentralAction D a q)

theorem native_central_fourier_reconstruction {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (ε : ℝ) (hε : 0 < ε) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
    ∃ c : (nativeNilmanifoldCenterIndex D → ℤ) →₀ ℂ,
      ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
        ‖F - c.sum (fun k a => a • nativeCentralFourierProjection D (-k) F)‖ < ε := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  let H := (fun p : C(D.G ⧸ D.Γ, ℂ) × (D.G ⧸ D.Γ) => nativeCentralOrbitObservable D p.1 p.2) ''
    (unitLipschitzObservables (D.G ⧸ D.Γ) ×ˢ Set.univ)
  have hbound : ∀ G ∈ H, ‖G‖ ≤ 1 := by
    rintro G ⟨⟨F,q⟩, ⟨hF, _⟩, rfl⟩
    exact native_central_unit_orbit_norm D F hF q
  obtain ⟨c, hc⟩ := compact_torus_fourier_kernel_reconstruction H
    (native_central_unit_orbit_family_compact D) hbound (ε/2) (by positivity)
  refine ⟨c, ?_⟩
  intro F hF
  have hpoint : ∀ q : D.G ⧸ D.Γ,
      ‖(F-c.sum (fun k a => a • nativeCentralFourierProjection D (-k) F)) q‖ < ε/2 := by
    intro q
    have h := hc (nativeCentralOrbitObservable D F q) ⟨(F,q), ⟨hF, Set.mem_univ q⟩, rfl⟩
    simp only [native_central_orbit_observable_apply, native_nilmanifold_central_action_zero] at h
    simpa only [Finsupp.sum, ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul, ContinuousMap.sub_apply,
      native_central_fourier_projection_apply, neg_neg] using h
  apply lt_of_le_of_lt ((ContinuousMap.norm_le _ (by positivity : 0 ≤ ε/2)).mpr
    (fun q => (hpoint q).le))
  linarith only [hε]

end Hindman168
