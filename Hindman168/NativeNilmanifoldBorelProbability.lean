import Hindman168.MeasurableSpaceMeasureTransport
import Hindman168.NativeNilmanifoldProbabilityUniqueness

/-! ORIGINAL canonical quotient probability under its PROVED identical Borel
sigma-algebra; genuine uniqueness and integrals survive actual transport. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

noncomputable def nativeNilmanifoldBorelProbability {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    @Measure (D.G ⧸ D.Γ) (borel (D.G ⧸ D.Γ)) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  exact measurableSpaceMeasureTransport (native_nilmanifold_coset_borel D).measurable_eq
    (nativeNilmanifoldQuotientProbability D)

theorem native_nilmanifold_borel_probability_isProbability {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace (D.G ⧸ D.Γ) := borel (D.G ⧸ D.Γ)
    IsProbabilityMeasure (nativeNilmanifoldBorelProbability D) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  exact measurable_space_measure_transport_probability
    (native_nilmanifold_coset_borel D).measurable_eq (nativeNilmanifoldQuotientProbability D)
    (native_nilmanifold_quotient_probability_isProbability D)

theorem native_nilmanifold_borel_probability_unique {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace (D.G ⧸ D.Γ) := borel (D.G ⧸ D.Γ)
    ∀ (ν : Measure (D.G ⧸ D.Γ)), IsProbabilityMeasure ν →
      (∀ g : D.G, Measure.map (fun q : D.G ⧸ D.Γ => g • q) ν = ν) →
        ν = nativeNilmanifoldBorelProbability D := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  let h := (native_nilmanifold_coset_borel D).measurable_eq
  intro ν hν hInv
  let ν' := measurableSpaceMeasureTransport h.symm ν
  have hp := measurable_space_measure_transport_probability h.symm ν hν
  have hi : ∀ g : D.G, Measure.map (fun q : D.G ⧸ D.Γ => g • q) ν' = ν' := by
    intro g
    rw [← measurable_space_measure_transport_map h.symm ν, hInv]
  have he := native_nilmanifold_invariant_probability_unique D ν' hp hi
  have ht := congrArg (measurableSpaceMeasureTransport h) he
  rw [measurable_space_measure_transport_inverse] at ht
  exact ht

theorem native_nilmanifold_borel_probability_integral {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    ∀ f : (D.G ⧸ D.Γ) → ℂ,
      (letI : MeasurableSpace (D.G ⧸ D.Γ) := borel (D.G ⧸ D.Γ);
        ∫ q, f q ∂nativeNilmanifoldBorelProbability D) =
      ∫ q, f q ∂nativeNilmanifoldQuotientProbability D := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  intro f
  exact measurable_space_measure_transport_integral (native_nilmanifold_coset_borel D).measurable_eq
    (nativeNilmanifoldQuotientProbability D) f

end Hindman168
