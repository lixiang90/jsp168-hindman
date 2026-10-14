import Hindman168.MasterRationalDenominators
import Hindman168.RationalWeightedMeanOne

/-!
# Actual master weighted mean-one for rational rows

The original prime-only event and original mixed base law are retained.
Denominator units follow from their smooth and actual prime-slot factors.
Integer-valuedness on the actual support remains explicit. Row hypotheses
are required only on the prime-law support. Restricting to that support
changes neither its event mass nor its weighted expectation.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

theorem event_restrict_support {α : Type*} (μ : Mass α) (E : α → Prop) :
    event μ (fun x => x ∈ μ.support ∧ E x) = event μ E := by
  unfold event
  apply Finset.sum_congr rfl
  intro x hx
  simp only [hx, true_and]

end Hindman168.FiniteMass

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def masterChainRationalWeightedMean {m q r d : ℕ}
    (F : MasterParameterFamily) (w : ℕ) (C : Chain m) (label : Fin q → Fin m)
    (gap : Fin r → ℕ) (base : (Fin r → ℕ) → Mass (Fin d → ℤ))
    (c : (Fin r → ℕ) → Fin q → Fin d → ℚ) (E : (Fin r → ℕ) → Prop) : ℝ :=
  expectation (masterPrimeSlotsMass F w gap) (fun x => if E x then expectation (base x)
    (fun y => ∏ u, rationalDivisorMask
      (tailMass (primorial w) (C.tailCutoffs (F.cutoff w) (label u)))
        (∑ j, c x u j * (y j : ℚ))) else 0)

theorem masterChainWeightedMean_restrict_support {m q r d : ℕ}
    (F : MasterParameterFamily) (w : ℕ) (C : Chain m) (label : Fin q → Fin m)
    (gap : Fin r → ℕ) (base : (Fin r → ℕ) → Mass (Fin d → ℤ))
    (b : (Fin r → ℕ) → Fin q → Fin d → ℤ) (E : (Fin r → ℕ) → Prop) :
    masterChainWeightedMean F w C label gap base b E =
      masterChainWeightedMean F w C label gap base b
        (fun x => x ∈ (masterPrimeSlotsMass F w gap).support ∧ E x) := by
  apply expectation_congr_support
  intro x hx
  simp only [hx, true_and]

theorem masterChainRationalWeightedMean_clear {m q r d : ℕ}
    (F : MasterParameterFamily) (w : ℕ) (C : Chain m) (label : Fin q → Fin m)
    (gap : Fin r → ℕ) (base : (Fin r → ℕ) → Mass (Fin d → ℤ))
    (c : (Fin r → ℕ) → Fin q → Fin d → ℚ) (den : (Fin r → ℕ) → Fin q → ℕ)
    (b : (Fin r → ℕ) → Fin q → Fin d → ℤ) (E : (Fin r → ℕ) → Prop)
    (hclear : ∀ x ∈ (masterPrimeSlotsMass F w gap).support, E x → ∀ u j,
      (den x u : ℚ) * c x u j = (b x u j : ℚ))
    (hvalue : ∀ x ∈ (masterPrimeSlotsMass F w gap).support, E x →
      ∀ y ∈ (base x).support, ∀ u, ∃ z : ℤ, (∑ j, c x u j * (y j : ℚ)) = (z : ℚ))
    (hunit : ∀ x ∈ (masterPrimeSlotsMass F w gap).support, E x → ∀ u,
      ∀ k ∈ (tailMass (primorial w) (C.tailCutoffs (F.cutoff w) (label u))).support,
        (den x u).Coprime k) :
    masterChainRationalWeightedMean F w C label gap base c E =
      masterChainWeightedMean F w C label gap base b E := by
  apply expectation_congr_support
  intro x hx
  by_cases he : E x
  · simp only [if_pos he]
    apply expectation_congr_support
    intro y hy
    exact Finset.prod_congr rfl (fun u _ => rational_row_mask_clear _ (c x u)
      (den x u) (b x u) (hclear x hx he u) y (hvalue x hx he y hy u) (hunit x hx he u))
  · simp only [if_neg he]

theorem MasterParameterConditions.chain_mixed_rational_weighted_mean_one_tendsto {n N m q r d L : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (C : ℕ → Chain m)
    (hN : ∀ w i, (C w).block i ⊆ Finset.range N) (label : ℕ → Fin q → Fin m)
    (gap : ℕ → Fin r → Fin L) (V : ℕ → ℕ) (hV : ∀ᶠ w in atTop, 1 ≤ V w)
    (hdivbudget : ∀ᶠ w in atTop, ∀ u, tailBound ((C w).tailCutoffs (F.cutoff w) (label w u)) ≤ V w)
    (hprimebudget : ∀ᶠ w in atTop, ∀ j, V w ≤ F.auxiliary w (gap w j))
    (T : Finset (MvPolynomial (Fin r) ℤ)) (hT : ∀ f ∈ T, f ≠ 0)
    (H : Finset (Fin d)) (index : ℕ → Fin d → Fin N)
    (Tmin : ℕ → Fin d → ℕ)
    (loc : ℕ → (Fin r → ℕ) → Fin d → ℤ)
    (len : ℕ → (Fin r → ℕ) → Fin d → ℕ)
    (c : ℕ → (Fin r → ℕ) → Fin q → Fin d → ℚ)
    (den smoothExp : ℕ → (Fin r → ℕ) → Fin q → ℕ)
    (slotExp : ℕ → (Fin r → ℕ) → Fin q → Fin r → ℕ)
    (b : ℕ → (Fin r → ℕ) → Fin q → Fin d → ℤ) (E : ℕ → (Fin r → ℕ) → Prop)
    (hharmbudget : ∀ᶠ w in atTop, ∀ j ∈ H, V w ≤ F.auxiliary w (index w j).val)
    (hlengthgrowth : ∀ j, j ∉ H → PowerDominates atTop (fun w => (Tmin w j : ℝ))
      (fun w => (samplingSize 0 (V w) 0 (V w) : ℝ)))
    (hlen : ∀ᶠ w in atTop, ∀ x, E w x → ∀ j, j ∉ H → Tmin w j ≤ len w x j)
    (hden : ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (fun j => gap w j)).support,
      E w x → ∀ u, den w x u ∣ (primorial w) ^ smoothExp w x u * ∏ j, x j ^ slotExp w x u j)
    (hclear : ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (fun j => gap w j)).support,
      E w x → ∀ u j, (den w x u : ℚ) * c w x u j = (b w x u j : ℚ))
    (hvalue : ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (fun j => gap w j)).support,
      E w x → ∀ y ∈ (masterMixedBaseMass H F index loc len w x).support, ∀ u,
        ∃ z : ℤ, (∑ j, c w x u j * (y j : ℚ)) = (z : ℚ))
    (hprimitive : ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (fun j => gap w j)).support,
      E w x → ∀ p : boundedRoughPrimeSet w (V w), ∀ u,
      ∃ j, unitDenominatorRow (p : ℕ) (den w x u) (b w x u) j ≠ 0)
    (hindependent : ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (fun j => gap w j)).support,
      E w x → ∀ p : boundedRoughPrimeSet w (V w),
      ¬ squarefreeCRTBadEvent (boundedRoughPrimeSet w (V w))
        (fun p hp => ((mem_boundedRoughPrimeSet w (V w) p).mp hp).1) T
          (fun j => (x j : ZMod (squarefreeCRTModulus (boundedRoughPrimeSet w (V w))))) p →
        ∀ u v, u ≠ v → LinearIndependent (ZMod (p : ℕ))
          ![(fun j => unitDenominatorRow (p : ℕ) (den w x u) (b w x u) j), (fun j => unitDenominatorRow (p : ℕ) (den w x v) (b w x v) j)]) :
    Tendsto (fun w => masterChainRationalWeightedMean F w (C w) (label w) (fun j => gap w j)
        (masterMixedBaseMass H F index loc len w) (c w) (E w) - event (masterPrimeSlotsMass F w (fun j => gap w j)) (E w))
      atTop (𝓝 0) := by
  let G := fun w x => x ∈ (masterPrimeSlotsMass F w (fun j => gap w j)).support ∧ E w x
  have hu := hF.chain_denominators_eventually_units C hN label gap V hdivbudget
    hprimebudget den smoothExp slotExp E hden
  have hp : ∀ᶠ w in atTop, ∀ x, G w x → ∀ p : boundedRoughPrimeSet w (V w), ∀ u,
      ∃ j, (b w x u j : ZMod (p : ℕ)) ≠ 0 := by
    filter_upwards [hu, hprimitive] with w huw hpw
    intro x hx p u
    exact (unitDenominatorRow_primitive_iff ((huw x hx.1 hx.2).2 p u) (b w x u)).mp
      (hpw x hx.1 hx.2 p u)
  have hi : ∀ᶠ w in atTop, ∀ x, G w x → ∀ p : boundedRoughPrimeSet w (V w),
      ¬ squarefreeCRTBadEvent (boundedRoughPrimeSet w (V w))
        (fun p hp => ((mem_boundedRoughPrimeSet w (V w) p).mp hp).1) T
          (fun j => (x j : ZMod (squarefreeCRTModulus (boundedRoughPrimeSet w (V w))))) p →
        ∀ u v, u ≠ v → LinearIndependent (ZMod (p : ℕ))
          ![(fun j => (b w x u j : ZMod (p : ℕ))), (fun j => (b w x v j : ZMod (p : ℕ))) ] := by
    filter_upwards [hu, hindependent] with w huw hiw
    intro x hx p hb u v huv
    exact (unitDenominatorRow_pairIndependent_iff ((huw x hx.1 hx.2).2 p u)
      ((huw x hx.1 hx.2).2 p v) (b w x u) (b w x v)).mp
        (hiw x hx.1 hx.2 p hb u v huv)
  have ht := hF.chain_mixed_weighted_mean_one_tendsto C hN label gap V hV
    hdivbudget hprimebudget T hT H index Tmin loc len b G hharmbudget hlengthgrowth
    (hlen.mono (fun w hw x hx => hw x hx.2)) hp hi
  have heq : ∀ᶠ w in atTop,
      masterChainRationalWeightedMean F w (C w) (label w) (fun j => gap w j)
        (masterMixedBaseMass H F index loc len w) (c w) (E w) -
          event (masterPrimeSlotsMass F w (fun j => gap w j)) (E w) =
      masterChainWeightedMean F w (C w) (label w) (fun j => gap w j)
        (masterMixedBaseMass H F index loc len w) (b w) (G w) -
          event (masterPrimeSlotsMass F w (fun j => gap w j)) (G w) := by
    filter_upwards [hu, hclear, hvalue] with w huw hcw hvw
    rw [masterChainRationalWeightedMean_clear F w (C w) (label w) (fun j => gap w j)
      (masterMixedBaseMass H F index loc len w) (c w) (den w) (b w) (E w) hcw hvw
      (fun x hx he => (huw x hx he).1), masterChainWeightedMean_restrict_support]
    rw [show event (masterPrimeSlotsMass F w (fun j => gap w j)) (G w) =
      event (masterPrimeSlotsMass F w (fun j => gap w j)) (E w) from event_restrict_support _ _]
  exact ht.congr' (heq.mono (fun _ hw => hw.symm))

end Hindman168
