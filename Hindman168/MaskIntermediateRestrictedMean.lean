import Hindman168.MaskIntermediateResidueCertificates
import Hindman168.MasterMixedWeightedMeanOne
import Hindman168.MasterRationalWeightedMeanOne

/-! Restricted divisor-weight means for any fixed monomial row family
under the unchanged mask-generated master, including every intermediate
mask-removal stage. No original good-event or catalogue inclusion is assumed. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskOriginalSampling

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N n r : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
  (hmono : F.MonomialStructure) (target : Fin r)

noncomputable def monomialRowWeight {q : ℕ} (label : ℕ → Fin q → Fin (m + 1))
    (row : ℕ → Fin q → Fin r)
    (w : ℕ) (u : Fin q) (x : Fin n → ℕ)
    (z : Fin (m + 1) → ℤ) : ℝ :=
  integerDivisorMask (tailMass (primorial w)
    ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w u)))
    (F.normalizedIntegerLinearForm x
      (masterColumnCoefficient N a (fun w => (C w).block) w) (row w u) z)

noncomputable def monomialRestrictedMean {q : ℕ} (label : ℕ → Fin q → Fin (m + 1))
    (row : ℕ → Fin q → Fin r)
    (E : ℕ → (Fin n → ℕ) → Prop) (w : ℕ) : ℝ :=
  conditionalFiniteAverage (monomialRowPrimeMass m gap n w) (fun _ => maskOriginalBaseMass m gap C w)
    (E w) (fun x z => ∏ u, monomialRowWeight gap a C F label row w u x z)

include ha hC hmono target in
theorem monomialRestrictedMean_tendsto_event {q : ℕ}
    (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → Fin q → Fin (m + 1))
    (row : ℕ → Fin q → Fin r)
    (hrow : ∀ᶠ w in atTop, Function.Injective (row w))
    (E : ℕ → (Fin n → ℕ) → Prop) :
    Tendsto (fun w => monomialRestrictedMean gap a C F label row E w -
      event (monomialRowPrimeMass m gap n w) (E w)) atTop (𝓝 0) := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  let index : ℕ → Fin (m + 1) → Fin N := fun w col =>
    ⟨(C w).pivot col, Finset.mem_range.mp (hC w col (by simp [Chain.block]))⟩
  let G := fun w x => x ∈ (monomialRowPrimeMass m gap n w).support ∧ E w x
  let c : ℕ → (Fin n → ℕ) →
      Fin q → Fin (m + 1) → ℤ := fun w x u j => F.normalizedIntegerRow x
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
  have hp := monomialRows_primitive_eventually gap a ha C hC F hmono
  have hi := monomialRows_independent_eventually gap a ha C hC F target
  have ht := hF.chain_mixed_weighted_mean_one_tendsto C hC label
    (fun w (_ : Fin n) => gap w)
    (fun w => (maskGeneratedMaster m gap).auxiliary w (gap w).val) hV hd
    (Eventually.of_forall (fun _ _ => le_rfl))
    (F.catalog target)
    (F.catalog_nonzero _)
    Finset.univ index (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) c G hh
    (fun _ hj => False.elim (hj (Finset.mem_univ _)))
    (Eventually.of_forall (fun _ _ _ _ hj => False.elim (hj (Finset.mem_univ _))))
    (hp.mono (fun w hw x hx p u => hw x hx.1 p (row w u)))
    (by
      filter_upwards [hi, hrow] with w hw hr
      intro x hx p hbad u v huv
      exact hw x hx.1 p hbad (row w u) (row w v) (fun he => huv (hr he)))
  have hbase (w : ℕ) (x : Fin n → ℕ) :
      masterMixedBaseMass Finset.univ (maskGeneratedMaster m gap) index
        (fun _ _ _ => 0) (fun _ _ _ => 0) w x = maskOriginalBaseMass m gap C w := by
    simp only [masterMixedBaseMass, mixedIntegerBaseMass, Finset.mem_univ, if_true,
      maskOriginalBaseMass, index]
  have he (w : ℕ) : monomialRestrictedMean gap a C F label row E w =
      masterChainWeightedMean (maskGeneratedMaster m gap) w (C w) (label w)
        (fun _ => (gap w).val)
        (masterMixedBaseMass Finset.univ (maskGeneratedMaster m gap) index
          (fun _ _ _ => 0) (fun _ _ _ => 0) w) (c w) (G w) := by
    unfold monomialRestrictedMean conditionalFiniteAverage masterChainWeightedMean
    apply expectation_congr_support
    intro x hx
    simp only [G, hx, true_and]
    rw [hbase]
    rfl
  exact ht.congr (fun w => by
    rw [← he w]
    change monomialRestrictedMean gap a C F label row E w -
        event (monomialRowPrimeMass m gap n w) (fun x => x ∈ (monomialRowPrimeMass m gap n w).support ∧ E w x) = _
    rw [event_restrict_support])

end Hindman168.MaskOriginalSampling
