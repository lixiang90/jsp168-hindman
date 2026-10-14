import Hindman168.MaskBaseResidueCertificates
import Hindman168.MasterMixedWeightedMeanOne
import Hindman168.MasterRationalWeightedMeanOne

/-! Mean-one for distinct actual base rows on any varying prime-only
restriction, including the full complement of the original good event.
The original unconditioned prime law and harmonic pivot laws are retained. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskOriginalSampling

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m)))

noncomputable def basePrimeMass (w : ℕ) : Mass (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) :=
  masterPrimeSlotsMass (maskGeneratedMaster m gap) w (fun _ => (gap w).val)

noncomputable def baseRowWeight {q : ℕ} (label : ℕ → Fin q → Fin (m + 1))
    (row : ℕ → Fin q → Fin (maskGeneratedRowDataFamily m gap t).rowCount)
    (w : ℕ) (u : Fin q) (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ)
    (z : Fin (m + 1) → ℤ) : ℝ :=
  integerDivisorMask (tailMass (primorial w)
    ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w u)))
    ((maskGeneratedRowDataFamily m gap t).rows.normalizedIntegerLinearForm x
      (masterColumnCoefficient N a (fun w => (C w).block) w) (row w u) z)

noncomputable def baseRestrictedMean {q : ℕ} (label : ℕ → Fin q → Fin (m + 1))
    (row : ℕ → Fin q → Fin (maskGeneratedRowDataFamily m gap t).rowCount)
    (E : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → Prop) (w : ℕ) : ℝ :=
  conditionalFiniteAverage (basePrimeMass gap t w) (fun _ => maskOriginalBaseMass m gap C w)
    (E w) (fun x z => ∏ u, baseRowWeight gap a C t label row w u x z)

include ha hC in
theorem baseRestrictedMean_tendsto_event {q : ℕ}
    (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → Fin q → Fin (m + 1))
    (row : ℕ → Fin q → Fin (maskGeneratedRowDataFamily m gap t).rowCount)
    (hrow : ∀ᶠ w in atTop, Function.Injective (row w))
    (E : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → Prop) :
    Tendsto (fun w => baseRestrictedMean gap a C t label row E w -
      event (basePrimeMass gap t w) (E w)) atTop (𝓝 0) := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  let index : ℕ → Fin (m + 1) → Fin N := fun w col =>
    ⟨(C w).pivot col, Finset.mem_range.mp (hC w col (by simp [Chain.block]))⟩
  let G := fun w x => x ∈ (basePrimeMass gap t w).support ∧ E w x
  let c : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) →
      Fin q → Fin (m + 1) → ℤ := fun w x u j => (maskGeneratedRowDataFamily m gap t).rows.normalizedIntegerRow x
    (masterColumnCoefficient N a (fun w => (C w).block) w) (row w u) j
  have hV : ∀ᶠ w in atTop, 1 ≤ (maskGeneratedMaster m gap).auxiliary w (gap w).val :=
    Eventually.of_forall (fun w => (by decide : 1 ≤ 2).trans
      ((maskGeneratedMaster m gap).auxiliary_ge_two w (gap w).val))
  have hd : ∀ᶠ w in atTop, ∀ u, tailBound ((C w).tailCutoffs
      ((maskGeneratedMaster m gap).cutoff w) (label w u)) ≤ (maskGeneratedMaster m gap).auxiliary w (gap w).val :=
    htail.mono (fun w hw u => hF.chain_tail_budget_at_gap (C w) w (label w u) (gap w).val (hw _))
  have hh : ∀ᶠ w in atTop, ∀ j ∈ (Finset.univ : Finset (Fin (m + 1))),
      (maskGeneratedMaster m gap).auxiliary w (gap w).val ≤
        (maskGeneratedMaster m gap).auxiliary w (index w j).val :=
    hgap.mono (fun w hw j _ => hF.auxiliary_monotone w (hw j))
  have hp := maskGenerated_base_rows_primitive gap a ha C hC t
  have hi := maskGenerated_base_rows_independent gap a ha C hC t
  have ht := hF.chain_mixed_weighted_mean_one_tendsto C hC label
    (fun w (_ : Fin (maskGeneratedRowDataFamily m gap t).arity) => gap w)
    (fun w => (maskGeneratedMaster m gap).auxiliary w (gap w).val) hV hd
    (Eventually.of_forall (fun _ _ => le_rfl))
    ((maskGeneratedRowDataFamily m gap t).rows.catalog (maskGeneratedRowDataFamily m gap t).target)
    ((maskGeneratedRowDataFamily m gap t).rows.catalog_nonzero _)
    Finset.univ index (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) c G hh
    (fun _ hj => False.elim (hj (Finset.mem_univ _)))
    (Eventually.of_forall (fun _ _ _ _ hj => False.elim (hj (Finset.mem_univ _))))
    (hp.mono (fun w hw x hx p u => hw x hx.1 p (row w u)))
    (by
      filter_upwards [hi, hrow] with w hw hr
      intro x hx p hbad u v huv
      exact hw x hx.1 p hbad (row w u) (row w v) (fun he => huv (hr he)))
  have hbase (w : ℕ) (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) :
      masterMixedBaseMass Finset.univ (maskGeneratedMaster m gap) index
        (fun _ _ _ => 0) (fun _ _ _ => 0) w x = maskOriginalBaseMass m gap C w := by
    simp only [masterMixedBaseMass, mixedIntegerBaseMass, Finset.mem_univ, if_true,
      maskOriginalBaseMass, index]
  have he (w : ℕ) : baseRestrictedMean gap a C t label row E w =
      masterChainWeightedMean (maskGeneratedMaster m gap) w (C w) (label w)
        (fun _ => (gap w).val)
        (masterMixedBaseMass Finset.univ (maskGeneratedMaster m gap) index
          (fun _ _ _ => 0) (fun _ _ _ => 0) w) (c w) (G w) := by
    unfold baseRestrictedMean conditionalFiniteAverage masterChainWeightedMean
    apply expectation_congr_support
    intro x hx
    simp only [G, hx, true_and]
    rw [hbase]
    rfl
  exact ht.congr (fun w => by
    rw [← he w]
    change baseRestrictedMean gap a C t label row E w -
        event (basePrimeMass gap t w) (fun x => x ∈ (basePrimeMass gap t w).support ∧ E w x) = _
    rw [event_restrict_support])

end Hindman168.MaskOriginalSampling
