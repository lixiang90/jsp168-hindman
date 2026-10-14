import Hindman168.FiniteEmpiricalProbability
import Hindman168.PositivePrincipalSumHarmonicCellGeometry

namespace Hindman168
open FiniteMass MeasureTheory
open scoped BigOperators Classical ENNReal

/-- The probability object in the actual point-mixture weak-limit theorem
is exactly the original finite uniform sampling event, with no normalization
or empty-window convention hidden in the conversion. -/
theorem principal_empirical_event_toReal {Z X : Type*} [MeasurableSpace X]
    (S : Finset Z) (hS : S.Nonempty) (orbit : Z → X) (fallback : X)
    (E : Set X) (hE : MeasurableSet E) :
    ((finiteEmpiricalProbability S orbit fallback : Measure X) E).toReal =
      event (uniformFinsetMass S) (fun z => orbit z ∈ E) := by
  simp only [finiteEmpiricalProbability, dif_pos hS, ProbabilityMeasure.coe_mk,
    finiteProbabilityMixture, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul,
    Measure.dirac_apply' _ hE, Set.indicator_apply, Pi.one_apply]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_sum (by intro i hi; split_ifs <;> simp)]
  simp only [Fintype.card_coe]
  rw [uniformFinsetMass, event_eq_sum _ _ (flatMass_support S _)]
  simp only [flatMass_apply]
  have hs : (∑ z ∈ S, if orbit z ∈ E then if z ∈ S then (S.card : ℝ)⁻¹ else 0 else 0) =
      ∑ z ∈ S, if orbit z ∈ E then (S.card : ℝ)⁻¹ else 0 := by
    apply Finset.sum_congr rfl
    intro z hz
    simp only [if_pos hz]
  rw [hs]
  rw [← Finset.sum_attach S (fun z => if orbit z ∈ E then (S.card : ℝ)⁻¹ else 0)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> simp
end Hindman168
