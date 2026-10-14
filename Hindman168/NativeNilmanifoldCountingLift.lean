import Hindman168.NativeNilmanifoldMeasurableSection
import Hindman168.CosetSectionCountingInvariance

/-! The actual original native section lifts any genuine invariant coset
probability to an actual sigma-finite left-invariant group measure. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

noncomputable def nativeNilmanifoldCountingLift {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.G := borel D.G
    Measure (D.G ⧸ D.Γ) → Measure D.G := by
  letI : MeasurableSpace D.G := borel D.G
  letI : BorelSpace D.G := ⟨rfl⟩
  letI := native_nilmanifold_group_polish D
  exact fun ν => cosetSectionCountingLift D.Γ (nativeNilmanifoldMeasurableSection D)
    (native_nilmanifold_section_right D) (native_nilmanifold_section_measurable D) ν

theorem native_nilmanifold_counting_lift_sigmaFinite {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.G := borel D.G
    ∀ (ν : Measure (D.G ⧸ D.Γ)), IsProbabilityMeasure ν → SigmaFinite (nativeNilmanifoldCountingLift D ν) := by
  letI : MeasurableSpace D.G := borel D.G
  letI : BorelSpace D.G := ⟨rfl⟩
  letI := native_nilmanifold_group_polish D
  letI := native_nilmanifold_lattice_countable D
  intro ν hν
  letI := hν
  exact coset_section_counting_lift_sigmaFinite D.Γ (nativeNilmanifoldMeasurableSection D)
    (native_nilmanifold_section_right D) (native_nilmanifold_section_measurable D) ν

theorem native_nilmanifold_counting_lift_leftInvariant {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.G := borel D.G
    ∀ (ν : Measure (D.G ⧸ D.Γ)),
      (∀ g : D.G, Measure.map (fun q : D.G ⧸ D.Γ => g • q) ν = ν) →
        Measure.IsMulLeftInvariant (nativeNilmanifoldCountingLift D ν) := by
  letI : MeasurableSpace D.G := borel D.G
  letI : BorelSpace D.G := ⟨rfl⟩
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_coset_borel D
  letI := native_nilmanifold_group_polish D
  letI := native_nilmanifold_lattice_countable D
  intro ν hν
  exact coset_section_counting_lift_leftInvariant D.Γ (nativeNilmanifoldMeasurableSection D)
    (native_nilmanifold_section_right D) (native_nilmanifold_section_measurable D) ν hν

end Hindman168
