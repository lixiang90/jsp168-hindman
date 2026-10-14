import Hindman168.PolynomialNullSets
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Actual atomless probability Haar measure on the p-adic integers

The additive Haar measure is normalized on the entire compact space. Its
singleton masses are zero because nonzero powers of p approach zero.
This is a real-valued measure-theory probability, not a p-adic-valued
functional from the unrelated Padics/Measure construction.
-/

namespace Hindman168

open MeasureTheory Filter TopologicalSpace
open scoped Topology

theorem padicInt_punctured_zero_neBot (p : ℕ) [Fact p.Prime] :
    (𝓝[≠] (0 : ℤ_[p])).NeBot := by
  have hp := Fact.out (p := p.Prime)
  have hp0 : (p : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hnorm : ‖(p : ℤ_[p])‖ < 1 := by
    rw [PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have ht := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnorm
  have ht' : Tendsto (fun n : ℕ => (p : ℤ_[p]) ^ n) atTop (𝓝[≠] (0 : ℤ_[p])) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨ht, Eventually.of_forall (fun n => ?_)⟩
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using pow_ne_zero n hp0
  exact (atTop_neBot.map _).mono ht'

variable (p : ℕ) [Fact p.Prime] [MeasurableSpace ℤ_[p]] [BorelSpace ℤ_[p]]

noncomputable def padicIntWholeCompact : PositiveCompacts ℤ_[p] :=
  ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

noncomputable def padicProbabilityHaar : Measure ℤ_[p] :=
  Measure.addHaarMeasure (padicIntWholeCompact p)

instance padicProbabilityHaar_isAddHaar : (padicProbabilityHaar p).IsAddHaarMeasure := by
  unfold padicProbabilityHaar
  infer_instance

instance padicProbabilityHaar_isProbability : IsProbabilityMeasure (padicProbabilityHaar p) := by
  constructor
  exact Measure.addHaarMeasure_self (K₀ := padicIntWholeCompact p)

instance padicProbabilityHaar_nullSingleton : NullSingletonClass (padicProbabilityHaar p) := by
  letI := padicInt_punctured_zero_neBot p
  infer_instance

theorem padicPolynomial_zero_measure {n : ℕ} (f : MvPolynomial (Fin n) ℤ_[p]) (hf : f ≠ 0) :
    (Measure.pi (fun _ : Fin n => padicProbabilityHaar p))
      {x | MvPolynomial.eval x f = 0} = 0 :=
  mvPolynomial_zero_set_measure_zero _ hf

end Hindman168
