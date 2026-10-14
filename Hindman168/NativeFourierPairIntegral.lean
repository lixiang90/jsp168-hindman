import Hindman168.NativeFourierPairFactorCompact
import Hindman168.NativeProductCanonicalIntegral

/-! Exact ORIGINAL canonical Haar mean of actual paired Fourier observable.
Nonzero frequencies have mean ZERO from true original product probability. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_fourier_pair_canonical_integral {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (k : nativeNilmanifoldCenterIndex D → ℤ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace (nativeNilmanifoldProduct D D).E := borel (nativeNilmanifoldProduct D D).E
    letI : MeasurableSpace (nativeNilmanifoldProduct D D).G := borel (nativeNilmanifoldProduct D D).G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ, ℂ),
      (∫ q, nativeFourierPairObservable D k F q ∂nativeNilmanifoldQuotientProbability (nativeNilmanifoldProduct D D)) =
        (∫ q, nativeCentralFourierProjection D k F q ∂nativeNilmanifoldQuotientProbability D) *
          star (∫ q, nativeCentralFourierProjection D k F q ∂nativeNilmanifoldQuotientProbability D) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace (nativeNilmanifoldProduct D D).E := borel (nativeNilmanifoldProduct D D).E
  letI : MeasurableSpace (nativeNilmanifoldProduct D D).G := borel (nativeNilmanifoldProduct D D).G
  letI : MeasurableSpace (D.G ⧸ D.Γ) := borel (D.G ⧸ D.Γ)
  letI := native_nilmanifold_borel_probability_isProbability D
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  rw [native_product_canonical_integral]
  change (∫ p, nativeFourierPairObservable D k F ((productCosetEquiv D.Γ D.Γ).symm p)
    ∂(nativeNilmanifoldBorelProbability D).prod (nativeNilmanifoldBorelProbability D)) = _
  have he : (fun p => nativeFourierPairObservable D k F ((productCosetEquiv D.Γ D.Γ).symm p)) =
      fun p => nativeCentralFourierProjection D k F p.1 * star (nativeCentralFourierProjection D k F p.2) := by
    funext p
    rw [native_fourier_pair_observable_apply]
    have h : productCosetMap D.Γ D.Γ ((productCosetEquiv D.Γ D.Γ).symm p) = p :=
      (productCosetEquiv D.Γ D.Γ).apply_symm_apply p
    rw [h]
  rw [he]
  rw [integral_prod_mul (μ := nativeNilmanifoldBorelProbability D) (ν := nativeNilmanifoldBorelProbability D)
    (fun q : D.G ⧸ D.Γ => nativeCentralFourierProjection D k F q)
    (fun q : D.G ⧸ D.Γ => star (nativeCentralFourierProjection D k F q))]
  have hs : (∫ q, star (nativeCentralFourierProjection D k F q) ∂nativeNilmanifoldBorelProbability D) =
      star (∫ q, nativeCentralFourierProjection D k F q ∂nativeNilmanifoldBorelProbability D) := by
    simpa only [Complex.star_def] using
      (integral_conj (μ := nativeNilmanifoldBorelProbability D) (f := fun q => nativeCentralFourierProjection D k F q))
  rw [hs]
  simp only [native_nilmanifold_borel_probability_integral]

theorem native_fourier_pair_nonzero_canonical_mean {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (k : nativeNilmanifoldCenterIndex D → ℤ) (hk : k ≠ 0) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace (nativeNilmanifoldProduct D D).E := borel (nativeNilmanifoldProduct D D).E
    letI : MeasurableSpace (nativeNilmanifoldProduct D D).G := borel (nativeNilmanifoldProduct D D).G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ, ℂ),
      (∫ q, nativeFourierPairObservable D k F q ∂nativeNilmanifoldQuotientProbability (nativeNilmanifoldProduct D D)) = 0 := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace (nativeNilmanifoldProduct D D).E := borel (nativeNilmanifoldProduct D D).E
  letI : MeasurableSpace (nativeNilmanifoldProduct D D).G := borel (nativeNilmanifoldProduct D D).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  rw [native_fourier_pair_canonical_integral,native_central_fourier_projection_nonzero_mean D k hk,zero_mul]

end Hindman168
