import Hindman168.NativeDiagonalQuotientData
import Hindman168.NativeFourierPairFactorIntegral
import Hindman168.NativeNilmanifoldBorelProbability

/-! ACTUAL diagonal-factor pushforward is the GENUINE newly constructed
native diagonal quotient canonical Haar; original nonnormal uniqueness
discharges the identification, not an assumed measure agreement. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u
attribute [local instance] diagonal_center_normal

theorem native_diagonal_factor_canonical_probability {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace (nativeNilmanifoldProduct D D).E := borel (nativeNilmanifoldProduct D D).E
    letI : MeasurableSpace (nativeNilmanifoldProduct D D).G := borel (nativeNilmanifoldProduct D D).G
    letI : MeasurableSpace (D.G × D.G) := borel (D.G × D.G)
    letI : MeasurableSpace (nativeDiagonalFactorSpace D) := borel (nativeDiagonalFactorSpace D)
    nativeDiagonalFactorProbability D = nativeNilmanifoldBorelProbability (nativeDiagonalQuotientData D) := by
  letI : MeasurableSpace (nativeNilmanifoldProduct D D).E := borel (nativeNilmanifoldProduct D D).E
  letI : MeasurableSpace (nativeNilmanifoldProduct D D).G := borel (nativeNilmanifoldProduct D D).G
  letI : MeasurableSpace (D.G × D.G) := borel (D.G × D.G)
  letI : MeasurableSpace (nativeDiagonalFactorSpace D) := borel (nativeDiagonalFactorSpace D)
  exact native_nilmanifold_borel_probability_unique (nativeDiagonalQuotientData D)
    (nativeDiagonalFactorProbability D) (native_diagonal_factor_probability_isProbability D)
    (native_diagonal_factor_probability_translate D)

theorem native_diagonal_pair_nonzero_canonical_mean {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (k : nativeNilmanifoldCenterIndex D → ℤ) (hk : k ≠ 0) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace (nativeNilmanifoldProduct D D).E := borel (nativeNilmanifoldProduct D D).E
    letI : MeasurableSpace (nativeNilmanifoldProduct D D).G := borel (nativeNilmanifoldProduct D D).G
    letI : MeasurableSpace (D.G × D.G) := borel (D.G × D.G)
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ, ℂ),
      (letI : MeasurableSpace (nativeDiagonalFactorSpace D) := borel (nativeDiagonalFactorSpace D);
        ∫ y, nativeFourierPairFactor D k F y ∂nativeNilmanifoldBorelProbability (nativeDiagonalQuotientData D)) = 0 := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace (nativeNilmanifoldProduct D D).E := borel (nativeNilmanifoldProduct D D).E
  letI : MeasurableSpace (nativeNilmanifoldProduct D D).G := borel (nativeNilmanifoldProduct D D).G
  letI : MeasurableSpace (D.G × D.G) := borel (D.G × D.G)
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  rw [← native_diagonal_factor_canonical_probability]
  exact native_fourier_pair_factor_nonzero_mean D k hk F

end Hindman168
