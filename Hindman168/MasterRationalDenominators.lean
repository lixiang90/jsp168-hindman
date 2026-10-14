import Hindman168.RoughDenominatorUnits
import Hindman168.MasterMixedWeightedMeanOne

/-!
# Derived denominator units on the actual master support

Denominators may divide any product of powers of primorial and of the
actual fresh prime slots. The exponents and denominators may vary with
the parameters. Both the original tail divisors and every tested rough
prime see these denominators as units; no additional unit conclusion is
assumed. Only the actual prime-law support is used.
-/

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

theorem master_chain_single_divisor_support {n N m : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (_hF : MasterParameterConditions N A D F) (C : Chain m) (w : ℕ)
    (hN : ∀ i, C.block i ⊆ Finset.range N)
    (hv : ∀ j ∈ Finset.range N, 2 ≤ F.cutoff w j ∧
      (primorial w : ℝ) / F.cutoff w j < Real.log (F.cutoff w j : ℝ))
    (i : Fin m) {k : ℕ}
    (hk : k ∈ (tailMass (primorial w) (C.tailCutoffs (F.cutoff w) i)).support) :
    0 < k ∧ k ≤ tailBound (C.tailCutoffs (F.cutoff w) i) ∧ (primorial w).Coprime k := by
  have hs := tailMass_support (C.tailCutoffs (F.cutoff w) i)
    (chain_tailCutoffs_valid C (F.cutoff w) (primorial w) hN hv i) k hk
  exact hs

theorem MasterParameterConditions.chain_denominators_eventually_units {n N m q r L : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (C : ℕ → Chain m)
    (hN : ∀ w i, (C w).block i ⊆ Finset.range N) (label : ℕ → Fin q → Fin m)
    (gap : ℕ → Fin r → Fin L) (V : ℕ → ℕ)
    (hdivbudget : ∀ᶠ w in atTop, ∀ u, tailBound ((C w).tailCutoffs (F.cutoff w) (label w u)) ≤ V w)
    (hprimebudget : ∀ᶠ w in atTop, ∀ j, V w ≤ F.auxiliary w (gap w j))
    (den smoothExp : ℕ → (Fin r → ℕ) → Fin q → ℕ)
    (slotExp : ℕ → (Fin r → ℕ) → Fin q → Fin r → ℕ) (E : ℕ → (Fin r → ℕ) → Prop)
    (hden : ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (fun j => gap w j)).support,
      E w x → ∀ u, den w x u ∣ (primorial w) ^ smoothExp w x u * ∏ j, x j ^ slotExp w x u j) :
    ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (fun j => gap w j)).support,
      E w x →
      (∀ u, ∀ k ∈ (tailMass (primorial w) ((C w).tailCutoffs (F.cutoff w) (label w u))).support,
        (den w x u).Coprime k) ∧
      (∀ p : boundedRoughPrimeSet w (V w), ∀ u, (den w x u).Coprime (p : ℕ)) := by
  filter_upwards [hF.raw_cutoffs_valid, hdivbudget,
    hF.prime_slots_eventually_gt_budget gap V hprimebudget, hden] with w hv hd hp hdenw
  intro x hx he
  have hxp := hp x hx
  refine ⟨?_, ?_⟩
  · intro u k hk
    have hs := master_chain_single_divisor_support hF (C w) w (hN w)
      (fun j hj => ⟨(hv j hj).1, (hv j hj).2.1⟩) (label w u) hk
    exact smooth_pool_denominator_coprime (smoothExp w x u) x (slotExp w x u) hxp
      hs.1 (hs.2.1.trans (hd u)) hs.2.2 (hdenw x hx he u)
  · intro p u
    have hs := (mem_boundedRoughPrimeSet w (V w) p).mp p.property
    exact smooth_pool_denominator_coprime (smoothExp w x u) x (slotExp w x u) hxp
      hs.1.pos hs.2.2 (prime_coprime_primorial_of_gt hs.1 hs.2.1).symm (hdenw x hx he u)

end Hindman168
