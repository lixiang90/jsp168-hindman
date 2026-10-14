import Hindman168.NativeCentralZeroIntegral
import Hindman168.NativeCentralFourierSelection

/-! The genuine zero-frequency branch is an ORIGINAL central-factor sample
discrepancy; nonzero-frequency means retain ORIGINAL samples and observables. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_central_zero_discrepancy_transfer {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    {α : Type*} (a : Finset α) (f : α → D.G ⧸ D.Γ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace (nativeCentralFactorSpace D) := borel (nativeCentralFactorSpace D)
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ, ℂ), nativeNilmanifoldFiniteDiscrepancy D a f (nativeCentralFourierProjection D 0 F) =
      finiteComplexSetMean a (fun x => nativeCentralZeroObservable D F (centralFactorCosetMap D.Γ (f x))) -
        ∫ y, nativeCentralZeroObservable D F y ∂nativeCentralFactorProbability D := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace (nativeCentralFactorSpace D) := borel (nativeCentralFactorSpace D)
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  change finiteComplexSetMean a (fun x => nativeCentralFourierProjection D 0 F (f x)) -
    (∫ q, nativeCentralFourierProjection D 0 F q ∂nativeNilmanifoldQuotientProbability D) = _
  rw [native_central_factor_zero_integral]
  simp only [native_central_zero_observable_apply]

theorem native_central_factor_or_nonzero_alternative {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (δ : ℝ) (hδ : 0 < δ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace (nativeCentralFactorSpace D) := borel (nativeCentralFactorSpace D)
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ M : ℕ, 0 < M ∧
      ∃ S : Finset (nativeNilmanifoldCenterIndex D → ℤ),
        (∀ k ∈ S, (∑ i, (k i).natAbs) ≤ M) ∧
        ∀ {α : Type*} (a : Finset α) (f : α → D.G ⧸ D.Γ),
          ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
            δ ≤ ‖nativeNilmanifoldFiniteDiscrepancy D a f F‖ →
              η ≤ ‖finiteComplexSetMean a (fun x => nativeCentralZeroObservable D F
                (centralFactorCosetMap D.Γ (f x))) -
                  ∫ y, nativeCentralZeroObservable D F y ∂nativeCentralFactorProbability D‖ ∨
              ∃ k ∈ S, k ≠ 0 ∧ η ≤ ‖finiteComplexSetMean a
                (fun x => nativeCentralFourierProjection D k F (f x))‖ := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace (nativeCentralFactorSpace D) := borel (nativeCentralFactorSpace D)
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨η, hη, hη1, M, hM, S, hS, h⟩ := native_central_fourier_bounded_alternative D δ hδ
  refine ⟨η, hη, hη1, M, hM, S, hS, ?_⟩
  intro α a f F hF hbad
  rcases h a f F hF hbad with hz | hn
  · exact Or.inl (by simpa only [native_central_zero_discrepancy_transfer] using hz)
  · exact Or.inr hn

end Hindman168
