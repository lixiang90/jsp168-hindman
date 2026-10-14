import Hindman168.NativeFourierPairFactor

/-! Genuine uniform-norm compactness of descended original pair family.
Descent is contractive on differences of actual paired observables; no
spatial Lipschitz property or decrease in nilpotency step is inferred. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_fourier_pair_factor_difference_bound {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (k : nativeNilmanifoldCenterIndex D → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace ((D.G × D.G) ⧸ D.Γ.prod D.Γ) := (nativeNilmanifoldProduct D D).quotientCompact
    letI : CompactSpace (nativeDiagonalFactorSpace D) := native_diagonal_factor_compact D
    ∀ F G : C(D.G ⧸ D.Γ, ℂ),
      ‖nativeFourierPairFactor D k F-nativeFourierPairFactor D k G‖ ≤
        ‖nativeFourierPairObservable D k F-nativeFourierPairObservable D k G‖ := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace ((D.G × D.G) ⧸ D.Γ.prod D.Γ) := (nativeNilmanifoldProduct D D).quotientCompact
  letI : CompactSpace (nativeDiagonalFactorSpace D) := native_diagonal_factor_compact D
  intro F G
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro y
  obtain ⟨q,rfl⟩ := (native_diagonal_factor_map_openQuotient D).surjective y
  simp only [ContinuousMap.sub_apply,native_fourier_pair_factor_apply]
  exact (nativeFourierPairObservable D k F-nativeFourierPairObservable D k G).norm_coe_le_norm q

theorem native_fourier_pair_factor_continuous {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (k : nativeNilmanifoldCenterIndex D → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    Continuous (nativeFourierPairFactor D k) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  letI : CompactSpace ((D.G × D.G) ⧸ D.Γ.prod D.Γ) := (nativeNilmanifoldProduct D D).quotientCompact
  letI : CompactSpace (nativeDiagonalFactorSpace D) := native_diagonal_factor_compact D
  apply Metric.continuous_iff.mpr
  intro F ε hε
  obtain ⟨δ,hδ,hClose⟩ := Metric.continuous_iff.mp (native_fourier_pair_observable_continuous D k) F ε hε
  refine ⟨δ,hδ,?_⟩
  intro G hG
  have h := native_fourier_pair_factor_difference_bound D k G F
  simp only [← dist_eq_norm] at h
  exact h.trans_lt (hClose G hG)

theorem native_fourier_pair_factor_family_compact {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (k : nativeNilmanifoldCenterIndex D → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    IsCompact (nativeFourierPairFactor D k '' unitLipschitzObservables (D.G ⧸ D.Γ)) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  exact (unit_lipschitz_observables_compact (D.G ⧸ D.Γ)).image (native_fourier_pair_factor_continuous D k)

theorem native_fourier_pair_factor_unit_bound {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (k : nativeNilmanifoldCenterIndex D → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ), ∀ y, ‖nativeFourierPairFactor D k F y‖ ≤ 1 := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  intro F hF y
  have hFN : ‖F‖ ≤ 1 := (ContinuousMap.norm_le F zero_le_one).mpr hF.2
  have hP : ∀ q, ‖nativeCentralFourierProjection D k F q‖ ≤ 1 := fun q =>
    ((nativeCentralFourierProjection D k F).norm_coe_le_norm q).trans
      ((native_central_fourier_projection_norm D k F).trans hFN)
  obtain ⟨q,rfl⟩ := (native_diagonal_factor_map_openQuotient D).surjective y
  rw [native_fourier_pair_factor_apply,native_fourier_pair_observable_apply,norm_mul,norm_star]
  simpa only [one_mul] using mul_le_mul (hP _) (hP _) (norm_nonneg _) zero_le_one

end Hindman168
