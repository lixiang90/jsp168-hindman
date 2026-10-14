import Hindman168.MaskRootSmoothedArithmetic
import Hindman168.MasterMixedWeightedMeanOne

/-! Mean-one for actual root-smoothed copied forms. The sampling contract
contains only the original master scales, divisor and prime budgets and
interval lengths. Arithmetic certificates are derived from the generated
mask family under its original fixed good-prime event. -/

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

set_option maxHeartbeats 2000000 in
structure MaskRootCopiedSampling (m N : ℕ) where
  gap : ℕ → Fin N
  a : Fin (m + 1) → ℚ
  positive : ∀ j, 0 < a j
  chain : ℕ → Chain (m + 1)
  blocks : ∀ w j, (chain w).block j ⊆ Finset.range N
  template : Fin (Fintype.card (LargeColumnSubset m))
  budget : ℕ → ℕ
  budget_pos : ∀ᶠ w in atTop, 1 ≤ budget w
  prime_budget : ∀ᶠ w in atTop, budget w ≤ (maskGeneratedMaster m gap).auxiliary w (gap w).val
  harmonic : Finset (MaskRootCopiedIndex m gap template)
  index : ℕ → MaskRootCopiedIndex m gap template → Fin N
  minimum : ℕ → MaskRootCopiedIndex m gap template → ℕ
  location : ℕ → (Fin (maskGeneratedRowDataFamily m gap template).arity → ℕ) → MaskRootCopiedIndex m gap template → ℤ
  length : ℕ → (Fin (maskGeneratedRowDataFamily m gap template).arity → ℕ) → MaskRootCopiedIndex m gap template → ℕ
  harmonic_budget : ∀ᶠ w in atTop, ∀ j ∈ harmonic,
    budget w ≤ (maskGeneratedMaster m gap).auxiliary w (index w j).val
  length_growth : ∀ j, j ∉ harmonic → PowerDominates atTop (fun w => (minimum w j : ℝ))
    (fun w => (samplingSize 0 (budget w) 0 (budget w) : ℝ))
  length_lower : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap template w x →
    ∀ j, j ∉ harmonic → minimum w j ≤ length w x j

namespace MaskRootCopiedSampling

variable {m N : ℕ}

noncomputable def primeMass (S : MaskRootCopiedSampling m N) (w : ℕ) :
    Mass (Fin (maskGeneratedRowDataFamily m S.gap S.template).arity → ℕ) :=
  masterPrimeSlotsMass (maskGeneratedMaster m S.gap) w (fun _ => (S.gap w).val)

noncomputable def baseMass (S : MaskRootCopiedSampling m N) (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m S.gap S.template).arity → ℕ) :
    Mass (MaskRootCopiedIndex m S.gap S.template → ℤ) :=
  masterMixedBaseMass S.harmonic (maskGeneratedMaster m S.gap) S.index S.location S.length w x

noncomputable def coefficient (S : MaskRootCopiedSampling m N) {q : ℕ}
    (row : ℕ → Fin q → MaskRootCopiedRow m S.gap S.template) (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m S.gap S.template).arity → ℕ)
    (u : Fin q) (j : MaskRootCopiedIndex m S.gap S.template) : ℤ :=
  (maskGeneratedRowDataFamily m S.gap S.template).rows.rootSmoothedFinIntegerCoefficient
    (maskGeneratedMaster m S.gap) w (masterColumnCoefficient N S.a (fun w => (S.chain w).block) w)
    x (maskGeneratedRowDataFamily m S.gap S.template).target (row w u) j

noncomputable def mean (S : MaskRootCopiedSampling m N) {q : ℕ}
    (label : ℕ → Fin q → Fin (m + 1)) (row : ℕ → Fin q → MaskRootCopiedRow m S.gap S.template)
    (w : ℕ) : ℝ :=
  masterChainWeightedMean (maskGeneratedMaster m S.gap) w (S.chain w) (label w)
    (fun _ => (S.gap w).val) (S.baseMass w) (S.coefficient row w)
    (maskGeneratedCopiedPrimeGood m S.gap S.template w)

set_option maxHeartbeats 2000000 in
theorem mean_one_tendsto (S : MaskRootCopiedSampling m N) {q : ℕ}
    (label : ℕ → Fin q → Fin (m + 1)) (row : ℕ → Fin q → MaskRootCopiedRow m S.gap S.template)
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
    exact (maskGeneratedRowDataFamily m S.gap S.template).rows.rootSmoothedFinIntegerCoefficient_primitive
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
    exact PolynomialRowFamily.rootSmoothedFinIntegerCoefficient_pair_independent H
      (hd S.template x hpool hx.2) (p : ℕ) hp.1 hp.2.1 (hp.2.2.trans hb)
      ((maskGeneratedRowDataFamily m S.gap S.template).rows.catalog_nonzero_of_not_squarefree_bad
        (maskGeneratedRowDataFamily m S.gap S.template).target _ _ x p hbad)
      (row w u) (row w v) (fun h => huv (hr h))

end MaskRootCopiedSampling
end Hindman168
