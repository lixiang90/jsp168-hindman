import Hindman168.NativeNilmanifoldCountingCompact
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! GENUINE group Haar uniqueness now applies to the ACTUAL finite-on-compacts
left-invariant counting lift. Quotient probability normalization remains. -/

namespace Hindman168
open MeasureTheory Measure
open scoped Manifold ContDiff NNReal
universe u

theorem native_nilmanifold_counting_lift_eq_haar_smul {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    ∀ (ν : Measure (D.G ⧸ D.Γ)), IsProbabilityMeasure ν →
      (∀ g : D.G, Measure.map (fun q : D.G ⧸ D.Γ => g • q) ν = ν) →
        ∃ c : ℝ≥0, nativeNilmanifoldCountingLift D ν = c • nativeNilmanifoldGroupHaar D := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : BorelSpace D.G := ⟨rfl⟩
  letI := native_nilmanifold_group_polish D
  letI := native_nilmanifold_group_locallyCompact D
  letI : SecondCountableTopology D.G :=
    (nativeLieGlobalExponentialHomeomorph (I := D.I) (G := D.G)).symm.secondCountableTopology
  letI := native_nilmanifold_group_haar_isHaar D
  intro ν hν hInv
  letI := native_nilmanifold_counting_lift_finiteOnCompacts D ν hν
  letI := native_nilmanifold_counting_lift_leftInvariant D ν hInv
  exact ⟨haarScalarFactor (nativeNilmanifoldCountingLift D ν) (nativeNilmanifoldGroupHaar D),
    isMulLeftInvariant_eq_smul _ _⟩

end Hindman168
