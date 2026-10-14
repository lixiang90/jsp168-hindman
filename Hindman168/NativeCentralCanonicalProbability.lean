import Hindman168.NativeNilmanifoldBorelProbability
import Hindman168.NativeCentralQuotientProjection
import Hindman168.NativeCentralZeroIntegral

/-! ACTUAL original central-factor pushforward probability equals the
GENUINE child native canonical Haar under PROVED common Borel structure. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_central_factor_canonical_probability {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace (nativeCentralFactorSpace D) := borel (nativeCentralFactorSpace D)
    nativeCentralFactorProbability D = nativeNilmanifoldBorelProbability (nativeCentralQuotientData D) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace (nativeCentralFactorSpace D) := borel (nativeCentralFactorSpace D)
  exact native_nilmanifold_borel_probability_unique (nativeCentralQuotientData D)
    (nativeCentralFactorProbability D) (native_central_factor_probability_isProbability D)
    (native_central_factor_probability_translate D)

theorem native_central_zero_child_integral {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ, ℂ),
      (letI : MeasurableSpace (nativeCentralFactorSpace D) := borel (nativeCentralFactorSpace D);
        ∫ y, nativeCentralZeroObservable D F y ∂nativeNilmanifoldBorelProbability (nativeCentralQuotientData D)) =
      ∫ q, F q ∂nativeNilmanifoldQuotientProbability D := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  rw [← native_central_factor_canonical_probability]
  exact native_central_zero_factor_original_integral D F

end Hindman168
