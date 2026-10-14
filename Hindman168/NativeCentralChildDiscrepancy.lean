import Hindman168.NativeCentralChildRegularFamily

/-! Exact zero-mode discrepancy in the actual CHILD metric and canonical Haar. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_central_child_zero_discrepancy {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    {α : Type*} (a : Finset α) (f : α → D.G ⧸ D.Γ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace (nativeCentralQuotientData D).E := borel (nativeCentralQuotientData D).E
    letI : MeasurableSpace (nativeCentralQuotientData D).G := borel (nativeCentralQuotientData D).G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeCentralQuotientData D).metric
    letI : TopologicalSpace ((nativeCentralQuotientData D).G ⧸ (nativeCentralQuotientData D).Γ) :=
      (nativeCentralQuotientData D).metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ, ℂ),
      nativeNilmanifoldFiniteDiscrepancy D a f (nativeCentralFourierProjection D 0 F) =
        nativeNilmanifoldFiniteDiscrepancy (nativeCentralQuotientData D) a
          (fun x => centralFactorCosetMap D.Γ (f x)) (nativeCentralChildZeroObservable D F) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace (nativeCentralQuotientData D).E := borel (nativeCentralQuotientData D).E
  letI : MeasurableSpace (nativeCentralQuotientData D).G := borel (nativeCentralQuotientData D).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeCentralQuotientData D).metric
  letI : TopologicalSpace ((nativeCentralQuotientData D).G ⧸ (nativeCentralQuotientData D).Γ) :=
    (nativeCentralQuotientData D).metric.toUniformSpace.toTopologicalSpace
  intro F
  exact native_central_zero_child_canonical_discrepancy D a f F

end Hindman168
