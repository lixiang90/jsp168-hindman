import Hindman168.NativeOriginalTerminalFourierCompactFamilies
import Hindman168.NativeMetricCosetTranslation
import Hindman168.NativeFourierPairObservable

/-! ACTUAL ORIGINAL terminal Fourier conjugate pairs, with arbitrary
first-coordinate ORIGINAL translation. Compact translation sets give true
uniform-norm compact families; no spatial regularity is assumed. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

noncomputable def nativeTerminalProductPairObservable {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (k : nativeOriginalTerminalIndex D d → ℤ) (g : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    C(D.G ⧸ D.Γ,ℂ) → C((D.G × D.G) ⧸ D.Γ.prod D.Γ,ℂ) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  exact (continuousConjugatePair ((nativeOriginalTerminalFourierProjection D d hd k F).comp
    (nativeMetricCosetTranslation D g)) (nativeOriginalTerminalFourierProjection D d hd k F)).comp
      (nativeProductMetricProjection D)

theorem native_terminal_product_pair_observable_apply {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (k : nativeOriginalTerminalIndex D d → ℤ) (g : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ,ℂ)) (q : (D.G × D.G) ⧸ D.Γ.prod D.Γ),
      nativeTerminalProductPairObservable D d hd k g F q =
        nativeOriginalTerminalFourierProjection D d hd k F (g • (productCosetMap D.Γ D.Γ q).1) *
          star (nativeOriginalTerminalFourierProjection D d hd k F (productCosetMap D.Γ D.Γ q).2) := by
  intro F q
  rfl

theorem native_terminal_product_pair_observable_continuous {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (k : nativeOriginalTerminalIndex D d → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    Continuous (fun p : D.G × C(D.G ⧸ D.Γ,ℂ) => nativeTerminalProductPairObservable D d hd k p.1 p.2) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  letI := productLattice_quotient_compact D.Γ D.Γ
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hp := (native_original_terminal_fourier_projection_functionspace_lipschitz D d hd k).continuous
  have hs : Continuous (fun p : (D.G × C(D.G ⧸ D.Γ,ℂ)) × ((D.G × D.G) ⧸ D.Γ.prod D.Γ) =>
      p.1.1 • (nativeProductMetricProjection D p.2).1) :=
    (native_metric_coset_action_continuous D).comp
      (continuous_fst.fst.prodMk (((nativeProductMetricProjection D).continuous.comp continuous_snd).fst))
  have h1 : Continuous (fun p : (D.G × C(D.G ⧸ D.Γ,ℂ)) × ((D.G × D.G) ⧸ D.Γ.prod D.Γ) =>
      nativeOriginalTerminalFourierProjection D d hd k p.1.2 (p.1.1 • (nativeProductMetricProjection D p.2).1)) :=
    continuous_eval.comp ((hp.comp continuous_fst.snd).prodMk hs)
  have h2 : Continuous (fun p : (D.G × C(D.G ⧸ D.Γ,ℂ)) × ((D.G × D.G) ⧸ D.Γ.prod D.Γ) =>
      nativeOriginalTerminalFourierProjection D d hd k p.1.2 (nativeProductMetricProjection D p.2).2) :=
    continuous_eval.comp ((hp.comp continuous_fst.snd).prodMk
      (((nativeProductMetricProjection D).continuous.comp continuous_snd).snd))
  exact h1.mul h2.star

theorem native_terminal_product_pair_family_compact {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (k : nativeOriginalTerminalIndex D d → ℤ)
    (K : Set D.G) (hK : IsCompact K) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    IsCompact ((fun p : D.G × C(D.G ⧸ D.Γ,ℂ) => nativeTerminalProductPairObservable D d hd k p.1 p.2) ''
      (K ×ˢ unitLipschitzObservables (D.G ⧸ D.Γ))) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  exact (hK.prod (unit_lipschitz_observables_compact (D.G ⧸ D.Γ))).image
    (native_terminal_product_pair_observable_continuous D d hd k)

theorem native_terminal_product_pair_unit_bound {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (k : nativeOriginalTerminalIndex D d → ℤ) (g : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ), ∀ q : (D.G × D.G) ⧸ D.Γ.prod D.Γ,
      ‖nativeTerminalProductPairObservable D d hd k g F q‖ ≤ 1 := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  intro F hF q
  have hnF : ‖F‖ ≤ 1 := (ContinuousMap.norm_le _ zero_le_one).mpr hF.2
  have hπ : ‖nativeOriginalTerminalFourierProjection D d hd k F‖ ≤ 1 :=
    (native_original_terminal_fourier_projection_norm D d hd k F).trans hnF
  rw [native_terminal_product_pair_observable_apply,norm_mul,norm_star]
  exact (mul_le_mul ((nativeOriginalTerminalFourierProjection D d hd k F).norm_coe_le_norm _ |>.trans hπ)
    ((nativeOriginalTerminalFourierProjection D d hd k F).norm_coe_le_norm _ |>.trans hπ)
    (norm_nonneg _) zero_le_one).trans (by norm_num)

end Hindman168
