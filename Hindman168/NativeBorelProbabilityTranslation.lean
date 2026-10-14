import Hindman168.NativeNilmanifoldBorelProbability

/-! The actual canonical probability in its PROVED Borel representation
retains original group translation invariance and continuous integrability. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_borel_probability_translate {s : ℕ} (D : NativeNilmanifoldData.{u} s) (g : D.G) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace (D.G ⧸ D.Γ) := borel (D.G ⧸ D.Γ)
    Measure.map (fun q : D.G ⧸ D.Γ => g • q) (nativeNilmanifoldBorelProbability D) =
      nativeNilmanifoldBorelProbability D := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace (D.G ⧸ D.Γ) := borel (D.G ⧸ D.Γ)
  let h := (native_nilmanifold_coset_borel D).measurable_eq
  change Measure.map _ (measurableSpaceMeasureTransport h _) = measurableSpaceMeasureTransport h _
  rw [← measurable_space_measure_transport_map h,
    native_nilmanifold_quotient_probability_translate]

theorem native_borel_probability_integrable {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace (D.G ⧸ D.Γ) := borel (D.G ⧸ D.Γ)
    ∀ F : C(D.G ⧸ D.Γ, ℂ), Integrable F (nativeNilmanifoldBorelProbability D) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace (D.G ⧸ D.Γ) := borel (D.G ⧸ D.Γ)
  letI : BorelSpace (D.G ⧸ D.Γ) := ⟨rfl⟩
  letI := native_nilmanifold_borel_probability_isProbability D
  intro F
  exact F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)

end Hindman168
