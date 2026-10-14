import Hindman168.CosetSectionCountingRecovery
import Hindman168.NativeNilmanifoldCountingHaarScalar

/-! ACTUAL native transversal and section discharge ALL counting-recovery
hypotheses and recover arbitrary ORIGINAL coset measure exactly. -/

namespace Hindman168
open Set MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_nilmanifold_section_mem_transversal {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (q : D.G ⧸ D.Γ) : nativeNilmanifoldMeasurableSection D q ∈ nativeNilmanifoldMeasurableTransversal D := by
  letI : MeasurableSpace D.G := borel D.G
  exact ((nativeNilmanifoldTransversalEquiv D).symm q).property

theorem native_nilmanifold_counting_transversal_mass {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.G := borel D.G
    ∀ ν : Measure (D.G ⧸ D.Γ), nativeNilmanifoldCountingLift D ν (nativeNilmanifoldMeasurableTransversal D) =
      ν Set.univ := by
  letI : MeasurableSpace D.G := borel D.G
  letI : BorelSpace D.G := ⟨rfl⟩
  letI := native_nilmanifold_group_polish D
  letI := native_nilmanifold_lattice_countable D
  intro ν
  have h := native_nilmanifold_measurable_transversal_spec D
  exact coset_section_counting_lift_transversal_mass D.Γ (nativeNilmanifoldMeasurableSection D)
    (native_nilmanifold_section_right D) (native_nilmanifold_section_measurable D)
    (nativeNilmanifoldMeasurableTransversal D) h.1 h.2.2.1
    (native_nilmanifold_section_mem_transversal D) ν

theorem native_nilmanifold_counting_transversal_probability_mass {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.G := borel D.G
    ∀ ν : Measure (D.G ⧸ D.Γ), IsProbabilityMeasure ν →
      nativeNilmanifoldCountingLift D ν (nativeNilmanifoldMeasurableTransversal D) = 1 := by
  letI : MeasurableSpace D.G := borel D.G
  intro ν hν
  letI := hν
  rw [native_nilmanifold_counting_transversal_mass, measure_univ]

theorem native_nilmanifold_counting_transversal_map {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.G := borel D.G
    ∀ ν : Measure (D.G ⧸ D.Γ),
      Measure.map ((↑) : D.G → D.G ⧸ D.Γ)
        ((nativeNilmanifoldCountingLift D ν).restrict (nativeNilmanifoldMeasurableTransversal D)) = ν := by
  letI : MeasurableSpace D.G := borel D.G
  letI : BorelSpace D.G := ⟨rfl⟩
  letI := native_nilmanifold_group_polish D
  letI := native_nilmanifold_lattice_countable D
  intro ν
  have h := native_nilmanifold_measurable_transversal_spec D
  exact coset_section_counting_lift_transversal_map D.Γ (nativeNilmanifoldMeasurableSection D)
    (native_nilmanifold_section_right D) (native_nilmanifold_section_measurable D)
    (nativeNilmanifoldMeasurableTransversal D) h.1 h.2.2.1
    (native_nilmanifold_section_mem_transversal D) ν

end Hindman168
