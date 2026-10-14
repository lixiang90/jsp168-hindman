import Hindman168.NativeRationalTerminalFourierCompactFamilies
import Hindman168.RoughNativeActionFreezing

/-! ACTUAL complex original Fourier signal has a uniform scalar LEFT
action modulus on bounded parameters, before all raw polynomials/samples.
Only true compactness/continuity is used; no spatial Lipschitz action or
spatial Lipschitz Fourier projection is assumed. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_fourier_scalar_freezing {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) (y : D.E) (B ε : ℝ) (hε : 0 < ε) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ η : ℝ, 0 < η ∧ ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
      ∀ (a b : ℝ) (q : D.G ⧸ D.Γ), |a| ≤ B → |b| ≤ B → |a-b| ≤ η →
        ‖nativeRationalTerminalFourierProjection D L k F
          (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (a • y) • q)-
            nativeRationalTerminalFourierProjection D L k F
              (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (b • y) • q)‖ < ε := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  let U := unitLipschitzObservables (D.G ⧸ D.Γ)
  letI : CompactSpace U := isCompact_iff_compactSpace.mp (unit_lipschitz_observables_compact (D.G ⧸ D.Γ))
  let X := (D.G ⧸ D.Γ) × U
  let f : ℝ × X → ℂ := fun p => nativeRationalTerminalFourierProjection D L k p.2.2.val
    (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (p.1 • y) • p.2.1)
  have hFourier : Continuous (nativeRationalTerminalFourierProjection D L k) :=
    (native_rational_terminal_fourier_projection_functionspace_lipschitz D L k).continuous
  have hf : Continuous f := continuous_eval.comp
    ((hFourier.comp (continuous_subtype_val.comp continuous_snd.snd)).prodMk
      ((rough_native_scalar_action_continuous D y).comp (continuous_fst.prodMk continuous_snd.fst)))
  obtain ⟨η,hη,hm⟩ := rough_compact_parameter_modulus f hf B (by positivity : 0 < ε/2)
  refine ⟨η,hη,?_⟩
  intro F hF a b q ha hb hab
  have hh := hm a b (q,⟨F,hF⟩) ha hb hab
  have he : ‖nativeRationalTerminalFourierProjection D L k F
      (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (a • y) • q)-
        nativeRationalTerminalFourierProjection D L k F
          (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (b • y) • q)‖ ≤ ε/2 := by
    simpa only [f,dist_eq_norm] using hh
  linarith

end Hindman168
