import Hindman168.PolynomialCopiedIntegerRows
import Hindman168.MasterMixedWeightedMeanOne

/-! Actual mask-generated copied forms under the original master prime and
mixed base laws. The sampling conditions contain scale and length budgets,
not primitive-row, independence, error-smallness or moment-limit premises. -/

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

abbrev MaskCopiedRow (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) :=
  PolynomialRowFamily.AdditiveCopy (maskGeneratedRowDataFamily m gap t).target

abbrev MaskCopiedIndex (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) :=
  Fin (Fintype.card (PolynomialRowFamily.AdditiveColumn (maskGeneratedRowDataFamily m gap t).target m))

noncomputable def maskGeneratedCopiedPrimeGood (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) : Prop :=
  x ∈ (masterPrimeSlotsMass (maskGeneratedMaster m gap) w (fun _ => (gap w).val)).support ∧
    predictionLocalPrimeGoodEvent (maskGeneratedMaster m gap)
      ((maskGeneratedRowDataFamily m gap t).rows.catalog (maskGeneratedRowDataFamily m gap t).target)
      ((maskGeneratedRowDataFamily m gap t).rows.denominator (maskGeneratedRowDataFamily m gap t).target) w x

set_option maxHeartbeats 2000000 in
structure MaskCopiedSampling (m N : ℕ) where
  gap : ℕ → Fin N
  a : Fin (m + 1) → ℚ
  positive : ∀ j, 0 < a j
  chain : ℕ → Chain (m + 1)
  blocks : ∀ w j, (chain w).block j ⊆ Finset.range N
  template : Fin (Fintype.card (LargeColumnSubset m))
  budget : ℕ → ℕ
  budget_pos : ∀ᶠ w in atTop, 1 ≤ budget w
  prime_budget : ∀ᶠ w in atTop, budget w ≤ (maskGeneratedMaster m gap).auxiliary w (gap w).val
  harmonic : Finset (MaskCopiedIndex m gap template)
  index : ℕ → MaskCopiedIndex m gap template → Fin N
  minimum : ℕ → MaskCopiedIndex m gap template → ℕ
  location : ℕ → (Fin (maskGeneratedRowDataFamily m gap template).arity → ℕ) → MaskCopiedIndex m gap template → ℤ
  length : ℕ → (Fin (maskGeneratedRowDataFamily m gap template).arity → ℕ) → MaskCopiedIndex m gap template → ℕ
  harmonic_budget : ∀ᶠ w in atTop, ∀ j ∈ harmonic,
    budget w ≤ (maskGeneratedMaster m gap).auxiliary w (index w j).val
  length_growth : ∀ j, j ∉ harmonic → PowerDominates atTop (fun w => (minimum w j : ℝ))
    (fun w => (samplingSize 0 (budget w) 0 (budget w) : ℝ))
  length_lower : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap template w x →
    ∀ j, j ∉ harmonic → minimum w j ≤ length w x j

namespace MaskCopiedSampling

variable {m N : ℕ}

noncomputable def primeMass (S : MaskCopiedSampling m N) (w : ℕ) :
    Mass (Fin (maskGeneratedRowDataFamily m S.gap S.template).arity → ℕ) :=
  masterPrimeSlotsMass (maskGeneratedMaster m S.gap) w (fun _ => (S.gap w).val)

noncomputable def baseMass (S : MaskCopiedSampling m N) (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m S.gap S.template).arity → ℕ) :
    Mass (MaskCopiedIndex m S.gap S.template → ℤ) :=
  masterMixedBaseMass S.harmonic (maskGeneratedMaster m S.gap) S.index S.location S.length w x

noncomputable def coefficient (S : MaskCopiedSampling m N) {q : ℕ}
    (row : ℕ → Fin q → MaskCopiedRow m S.gap S.template) (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m S.gap S.template).arity → ℕ)
    (u : Fin q) (j : MaskCopiedIndex m S.gap S.template) : ℤ :=
  (maskGeneratedRowDataFamily m S.gap S.template).rows.copiedFinIntegerCoefficient
    (maskGeneratedMaster m S.gap) w (masterColumnCoefficient N S.a (fun w => (S.chain w).block) w)
    x (maskGeneratedRowDataFamily m S.gap S.template).target (row w u) j

noncomputable def mean (S : MaskCopiedSampling m N) {q : ℕ}
    (label : ℕ → Fin q → Fin (m + 1)) (row : ℕ → Fin q → MaskCopiedRow m S.gap S.template)
    (w : ℕ) : ℝ :=
  masterChainWeightedMean (maskGeneratedMaster m S.gap) w (S.chain w) (label w)
    (fun _ => (S.gap w).val) (S.baseMass w) (S.coefficient row w)
    (maskGeneratedCopiedPrimeGood m S.gap S.template w)

set_option maxHeartbeats 2000000 in
theorem mean_one_tendsto (S : MaskCopiedSampling m N) {q : ℕ}
    (label : ℕ → Fin q → Fin (m + 1)) (row : ℕ → Fin q → MaskCopiedRow m S.gap S.template)
    (hrow : ∀ᶠ w in atTop, Function.Injective (row w))
    (hdivbudget : ∀ᶠ w in atTop, ∀ u,
      tailBound ((S.chain w).tailCutoffs ((maskGeneratedMaster m S.gap).cutoff w) (label w u)) ≤ S.budget w) :
    Tendsto (fun w => S.mean label row w -
      event (S.primeMass w) (maskGeneratedCopiedPrimeGood m S.gap S.template w)) atTop (𝓝 0) := by
  have hA : ∀ a ∈ Finset.univ.image S.a, 0 < a := by
    intro a ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
    exact S.positive j
  have hF := maskGeneratedMaster_conditions m S.gap (Finset.univ.image S.a) hA
  apply hF.chain_mixed_weighted_mean_one_tendsto S.chain S.blocks label
    (fun w _ => S.gap w) S.budget S.budget_pos hdivbudget
    (S.prime_budget.mono (fun w hw _ => hw))
    ((maskGeneratedRowDataFamily m S.gap S.template).rows.catalog (maskGeneratedRowDataFamily m S.gap S.template).target)
    ((maskGeneratedRowDataFamily m S.gap S.template).rows.catalog_nonzero _)
    S.harmonic S.index S.minimum S.location S.length (S.coefficient row)
    (maskGeneratedCopiedPrimeGood m S.gap S.template)
    S.harmonic_budget S.length_growth S.length_lower
  · filter_upwards [maskGenerated_chain_integer_row_directions m S.gap S.a S.positive S.chain S.blocks,
      S.prime_budget] with w hd hb
    intro x hx p u
    have hp := (mem_boundedRoughPrimeSet w (S.budget w) (p : ℕ)).mp p.property
    have hpool : x ∈ (primeIndependentMass (maskGeneratedRowDataFamily m S.gap S.template).arity
        ((maskGeneratedMaster m S.gap).pool w (S.gap w).val).lower
        ((maskGeneratedMaster m S.gap).pool w (S.gap w).val).upper).support := hx.1
    exact (maskGeneratedRowDataFamily m S.gap S.template).rows.copiedFinIntegerCoefficient_primitive
      (maskGeneratedMaster m S.gap) w _ x _ (hd S.template x hpool hx.2)
      (p : ℕ) hp.1 (hp.2.2.trans hb) (row w u)
  · filter_upwards [maskGenerated_chain_integer_row_directions m S.gap S.a S.positive S.chain S.blocks,
      maskGenerated_additive_elimination_data m S.gap S.a S.positive S.chain S.blocks,
      S.prime_budget, hrow] with w hd he hb hr
    intro x hx p hbad u v huv
    have hp := (mem_boundedRoughPrimeSet w (S.budget w) (p : ℕ)).mp p.property
    have hpool : x ∈ (primeIndependentMass (maskGeneratedRowDataFamily m S.gap S.template).arity
        ((maskGeneratedMaster m S.gap).pool w (S.gap w).val).lower
        ((maskGeneratedMaster m S.gap).pool w (S.gap w).val).upper).support := hx.1
    obtain ⟨H⟩ := he S.template x hx.2
    exact PolynomialRowFamily.copiedFinIntegerCoefficient_pair_independent H
      (hd S.template x hpool hx.2) (p : ℕ) hp.1 hp.2.1 (hp.2.2.trans hb)
      ((maskGeneratedRowDataFamily m S.gap S.template).rows.catalog_nonzero_of_not_squarefree_bad
        (maskGeneratedRowDataFamily m S.gap S.template).target _ _ x p hbad)
      (row w u) (row w v) (fun h => huv (hr h))

end MaskCopiedSampling
end Hindman168
