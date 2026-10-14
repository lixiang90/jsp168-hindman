import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Basic

/-! Explicit genuine transport along PROVED equality of sigma-algebras,
retaining all measure values, maps, probability and integrals. -/

namespace Hindman168
open MeasureTheory

noncomputable def measurableSpaceMeasureTransport {X : Type*} {m n : MeasurableSpace X}
    (h : m=n) (μ : @Measure X m) : @Measure X n :=
  Eq.mp (congrArg (fun r : MeasurableSpace X => @Measure X r) h) μ

theorem measurable_space_measure_transport_apply {X : Type*} {m n : MeasurableSpace X}
    (h : m=n) (μ : @Measure X m) (A : Set X) : measurableSpaceMeasureTransport h μ A = μ A := by
  cases h
  rfl

theorem measurable_space_measure_transport_probability {X : Type*} {m n : MeasurableSpace X}
    (h : m=n) (μ : @Measure X m) (hμ : @IsProbabilityMeasure X m μ) :
    @IsProbabilityMeasure X n (measurableSpaceMeasureTransport h μ) := by
  cases h
  exact hμ

theorem measurable_space_measure_transport_map {X : Type*} {m n : MeasurableSpace X}
    (h : m=n) (μ : @Measure X m) (f : X → X) :
    measurableSpaceMeasureTransport h (@Measure.map X X m m f μ) =
      @Measure.map X X n n f (measurableSpaceMeasureTransport h μ) := by
  cases h
  rfl

theorem measurable_space_measure_transport_inverse {X : Type*} {m n : MeasurableSpace X}
    (h : m=n) (μ : @Measure X n) :
    measurableSpaceMeasureTransport h (measurableSpaceMeasureTransport h.symm μ) = μ := by
  cases h
  rfl

theorem measurable_space_measure_transport_integral {X : Type*} {m n : MeasurableSpace X}
    (h : m=n) (μ : @Measure X m) (f : X → ℂ) :
    (letI : MeasurableSpace X := n; ∫ x, f x ∂measurableSpaceMeasureTransport h μ) =
      (letI : MeasurableSpace X := m; ∫ x, f x ∂μ) := by
  cases h
  rfl

end Hindman168
