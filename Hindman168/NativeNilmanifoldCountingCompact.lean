import Hindman168.CosetSectionCountingCompactMass
import Hindman168.NativeNilmanifoldCountingLift

/-! Native actual compact section range supplies ALL compact mass bounds. -/

namespace Hindman168
open Set MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_nilmanifold_counting_lift_finiteOnCompacts {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.G := borel D.G
    ∀ (ν : Measure (D.G ⧸ D.Γ)), IsProbabilityMeasure ν →
      IsFiniteMeasureOnCompacts (nativeNilmanifoldCountingLift D ν) := by
  letI : MeasurableSpace D.G := borel D.G
  letI : BorelSpace D.G := ⟨rfl⟩
  letI := native_nilmanifold_group_polish D
  letI := native_nilmanifold_lattice_countable D
  intro ν hν
  letI := hν
  obtain ⟨K, hK, hτK⟩ := native_nilmanifold_section_compact_bound D
  exact coset_section_counting_lift_finiteOnCompacts D.Γ Subgroup.isClosed_of_discrete
    (nativeNilmanifoldMeasurableSection D) (native_nilmanifold_section_right D)
    (native_nilmanifold_section_measurable D) ν K hK hτK

theorem native_nilmanifold_counting_lift_compact_mass {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.G := borel D.G
    ∀ (ν : Measure (D.G ⧸ D.Γ)), IsProbabilityMeasure ν →
      ∀ (C : Set D.G), IsCompact C → nativeNilmanifoldCountingLift D ν C < ⊤ := by
  letI : MeasurableSpace D.G := borel D.G
  intro ν hν C hC
  letI := native_nilmanifold_counting_lift_finiteOnCompacts D ν hν
  exact hC.measure_lt_top

end Hindman168
