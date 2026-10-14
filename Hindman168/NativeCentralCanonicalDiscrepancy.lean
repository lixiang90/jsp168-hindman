import Hindman168.NativeCentralCanonicalProbability
import Hindman168.NativeCentralZeroDiscrepancy

/-! ORIGINAL zero-mode mean/discrepancy use the ACTUAL child canonical Haar,
not an unproved invariant factor measure or replacement samples. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_central_zero_child_canonical_integral {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace (nativeCentralQuotientData D).E := borel (nativeCentralQuotientData D).E
    letI : MeasurableSpace (nativeCentralQuotientData D).G := borel (nativeCentralQuotientData D).G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ, ℂ),
      (∫ y, nativeCentralZeroObservable D F y ∂nativeNilmanifoldQuotientProbability (nativeCentralQuotientData D)) =
        ∫ q, F q ∂nativeNilmanifoldQuotientProbability D := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace (nativeCentralQuotientData D).E := borel (nativeCentralQuotientData D).E
  letI : MeasurableSpace (nativeCentralQuotientData D).G := borel (nativeCentralQuotientData D).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  rw [← native_nilmanifold_borel_probability_integral (nativeCentralQuotientData D)]
  exact native_central_zero_child_integral D F

theorem native_central_zero_child_canonical_discrepancy {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    {α : Type*} (a : Finset α) (f : α → D.G ⧸ D.Γ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace (nativeCentralQuotientData D).E := borel (nativeCentralQuotientData D).E
    letI : MeasurableSpace (nativeCentralQuotientData D).G := borel (nativeCentralQuotientData D).G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ, ℂ),
      nativeNilmanifoldFiniteDiscrepancy D a f (nativeCentralFourierProjection D 0 F) =
        finiteComplexSetMean a (fun x => nativeCentralZeroObservable D F (centralFactorCosetMap D.Γ (f x))) -
          ∫ y, nativeCentralZeroObservable D F y ∂nativeNilmanifoldQuotientProbability (nativeCentralQuotientData D) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace (nativeCentralQuotientData D).E := borel (nativeCentralQuotientData D).E
  letI : MeasurableSpace (nativeCentralQuotientData D).G := borel (nativeCentralQuotientData D).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  rw [native_central_zero_child_canonical_integral]
  change finiteComplexSetMean a (fun x => nativeCentralFourierProjection D 0 F (f x)) -
    (∫ q, nativeCentralFourierProjection D 0 F q ∂nativeNilmanifoldQuotientProbability D) = _
  rw [native_central_zero_projection_integral]
  simp only [native_central_zero_observable_apply]

end Hindman168
