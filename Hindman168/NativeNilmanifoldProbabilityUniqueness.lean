import Hindman168.NativeNilmanifoldTransversalDomain

/-! GENUINE uniqueness of invariant probability on ORIGINAL NONNORMAL cosets.
Actual counting recovery, group Haar uniqueness and unit mass normalize it. -/

namespace Hindman168
open Set MeasureTheory Measure
open scoped Manifold ContDiff NNReal ENNReal
universe u

theorem native_nilmanifold_invariant_probability_transversal {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    ∀ (ν : Measure (D.G ⧸ D.Γ)), IsProbabilityMeasure ν →
      (∀ g : D.G, Measure.map (fun q : D.G ⧸ D.Γ => g • q) ν = ν) →
        ν = fundamentalCosetProbability D.Γ (nativeNilmanifoldGroupHaar D) (nativeNilmanifoldMeasurableTransversal D) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  intro ν hν hInv
  obtain ⟨c, hc⟩ := native_nilmanifold_counting_lift_eq_haar_smul D ν hν hInv
  have hm := native_nilmanifold_counting_transversal_probability_mass D ν hν
  rw [hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hm
  have hcInv := ENNReal.eq_inv_of_mul_eq_one_left hm
  have hp := native_nilmanifold_counting_transversal_map D ν
  rw [hc, Measure.restrict_smul, Measure.map_smul, ENNReal.smul_def, hcInv] at hp
  exact hp.symm

theorem native_nilmanifold_invariant_probability_unique {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    ∀ (ν : Measure (D.G ⧸ D.Γ)), IsProbabilityMeasure ν →
      (∀ g : D.G, Measure.map (fun q : D.G ⧸ D.Γ => g • q) ν = ν) →
        ν = nativeNilmanifoldQuotientProbability D := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  intro ν hν hInv
  exact (native_nilmanifold_invariant_probability_transversal D ν hν hInv).trans
    (native_nilmanifold_transversal_canonical_probability D)

end Hindman168
