import Hindman168.NativeMetricCosetTranslation
import Hindman168.NativeOriginalTerminalFourierProjection
import Hindman168.RoughGroupBasepointNormalization

/-! Actual original translated basepoint observables, compact families in
the SAME specified metric and unchanged original terminal Fourier modes.
Uniform spatial Lipschitz translation is not assumed. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

noncomputable def nativeBasepointObservable {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (r : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    C(D.G ⧸ D.Γ,ℂ) → C(D.G ⧸ D.Γ,ℂ) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  exact F.comp (nativeMetricCosetTranslation D r)

theorem native_basepoint_observable_apply {s : ℕ} (D : NativeNilmanifoldData.{u} s) (r : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ,ℂ)) (q : D.G ⧸ D.Γ), nativeBasepointObservable D r F q = F (r • q) := by
  intro F q
  rfl

theorem native_basepoint_observable_continuous {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    Continuous (fun p : D.G × C(D.G ⧸ D.Γ,ℂ) => nativeBasepointObservable D p.1 p.2) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_eval.comp (continuous_fst.snd.prodMk
    ((native_metric_coset_action_continuous D).comp (continuous_fst.fst.prodMk continuous_snd)))

theorem native_basepoint_observable_family_compact {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (K : Set D.G) (hK : IsCompact K) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    IsCompact ((fun p : D.G × C(D.G ⧸ D.Γ,ℂ) => nativeBasepointObservable D p.1 p.2) ''
      (K ×ˢ unitLipschitzObservables (D.G ⧸ D.Γ))) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  exact (hK.prod (unit_lipschitz_observables_compact (D.G ⧸ D.Γ))).image
    (native_basepoint_observable_continuous D)

theorem native_basepoint_observable_unit_bound {s : ℕ} (D : NativeNilmanifoldData.{u} s) (r : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ), ∀ q : D.G ⧸ D.Γ,
      ‖nativeBasepointObservable D r F q‖ ≤ 1 := by
  intro F hF q
  exact hF.2 (r • q)

theorem native_basepoint_observable_terminal_projection {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (k : nativeOriginalTerminalIndex D d → ℤ) (r : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ,ℂ),
      nativeOriginalTerminalFourierProjection D d hd k (nativeBasepointObservable D r F) =
      nativeBasepointObservable D r (nativeOriginalTerminalFourierProjection D d hd k F) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  ext q
  rw [native_original_terminal_fourier_projection_apply,native_basepoint_observable_apply,
    native_original_terminal_fourier_projection_apply]
  apply integral_congr_ae
  filter_upwards with a
  simp only [native_basepoint_observable_apply,native_original_terminal_action_commutes]

theorem native_basepoint_observable_canonical_integral {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (r : D.G) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ,ℂ),
      (∫ q, nativeBasepointObservable D r F q ∂nativeNilmanifoldQuotientProbability D) =
        ∫ q, F q ∂nativeNilmanifoldQuotientProbability D := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  exact native_nilmanifold_probability_integral_translation D r F

end Hindman168
