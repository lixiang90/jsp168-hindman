import Hindman168.SquarefreeWeightedLinearForms
import Hindman168.MasterChainExcess

/-!
# Weighted integer linear forms under the actual master laws

Both the tail-divisor and fresh prime-slot laws are the original finite
laws. The master prime residue error is derived at the squarefree CRT
modulus, while the base comparison retains the true divisor product.
The application-specific primitive and separated-row conditions and the
original base residue error remain explicit. Their analytic combination
has no assumed prime-parameter or CRT-moment small-error conclusion.
-/

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def masterChainDivisorMass {m q : ℕ} (F : MasterParameterFamily) (w : ℕ)
    (C : Chain m) (label : Fin q → Fin m) : Mass (Fin q → ℕ) :=
  piMass (fun i => tailMass (primorial w) (C.tailCutoffs (F.cutoff w) (label i)))

noncomputable def masterChainWeightedMean {m q r d : ℕ} (F : MasterParameterFamily) (w : ℕ)
    (C : Chain m) (label : Fin q → Fin m) (gap : Fin r → ℕ)
    (base : (Fin r → ℕ) → Mass (Fin d → ℤ))
    (c : (Fin r → ℕ) → Fin q → Fin d → ℤ) (E : (Fin r → ℕ) → Prop) : ℝ :=
  expectation (masterPrimeSlotsMass F w gap) (fun x => if E x then expectation (base x)
    (fun y => ∏ u, integerDivisorMask
      (tailMass (primorial w) (C.tailCutoffs (F.cutoff w) (label u)))
        (∑ j, c x u j * y j)) else 0)

theorem MasterParameterConditions.chain_squarefree_weighted_error {n N m q r d : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (w V : ℕ) (C : Chain m)
    (hN : ∀ i, C.block i ⊆ Finset.range N) (label : Fin q → Fin m) (gap : Fin r → ℕ)
    (hv : ∀ j ∈ Finset.range N, 2 ≤ F.cutoff w j ∧
      0 < harmonicNormalizer (F.cutoff w j) (primorial w))
    (hdivbudget : ∀ u, tailBound (C.tailCutoffs (F.cutoff w) (label u)) ≤ V)
    (hprimebudget : ∀ j, V ≤ F.auxiliary w (gap j))
    (T : Finset (MvPolynomial (Fin r) ℤ))
    (base : (Fin r → ℕ) → Mass (Fin d → ℤ))
    (c : (Fin r → ℕ) → Fin q → Fin d → ℤ) (E : (Fin r → ℕ) → Prop)
    (εbase : ℝ) (hεbase : 0 ≤ εbase)
    (hprimitive : ∀ x, E x → ∀ p : boundedRoughPrimeSet w V, ∀ u,
      ∃ j, (c x u j : ZMod (p : ℕ)) ≠ 0)
    (hindependent : ∀ x, E x → ∀ p : boundedRoughPrimeSet w V,
      ¬ squarefreeCRTBadEvent (boundedRoughPrimeSet w V)
        (fun p hp => ((mem_boundedRoughPrimeSet w V p).mp hp).1) T
          (fun j => (x j : ZMod (squarefreeCRTModulus (boundedRoughPrimeSet w V)))) p →
        ∀ u v, u ≠ v → LinearIndependent (ZMod (p : ℕ))
          ![(fun j => (c x u j : ZMod (p : ℕ))), (fun j => (c x v j : ZMod (p : ℕ)))])
    (hbase : ∀ x, E x → ∀ k ∈ (masterChainDivisorMass F w C label).support,
      ∀ hprod : (∏ u, k u) ≠ 0,
        letI : NeZero (∏ u, k u) := ⟨hprod⟩
        distance ((base x).mapDomain (fun y j => (y j : ZMod (∏ u, k u))))
          (uniformFintypeMass (Fin d → ZMod (∏ u, k u))) ≤ εbase) :
    |masterChainWeightedMean F w C label gap base c E - event (masterPrimeSlotsMass F w gap) E| ≤
      expectation (masterChainDivisorMass F w C label)
        (comparisonPrimePowerCRTIntegrand (boundedRoughPrimeSet w V)
          (fun p hp => ((mem_boundedRoughPrimeSet w V p).mp hp).1) T) +
        ((V ^ q : ℕ) : ℝ) * (εbase + masterPrimeSlotsResidueError F w gap) := by
  let S := boundedRoughPrimeSet w V
  have hS : ∀ p ∈ S, p.Prime := fun p hp => ((mem_boundedRoughPrimeSet w V p).mp hp).1
  let ρ := fun u => tailMass (primorial w) (C.tailCutoffs (F.cutoff w) (label u))
  have hH (u : Fin q) (j : C.tail (label u)) :
      0 < harmonicNormalizer (F.cutoff w j) (primorial w) :=
    (hv j (hN (label u) (Finset.mem_insert_of_mem j.property))).2
  have hρ (u : Fin q) : ∀ k, 0 ≤ ρ u k := by
    rw [show ρ u = harmonicDivisorMass (fun j : C.tail (label u) => F.cutoff w j) (primorial w)
      from (harmonicDivisorMass_chain_tail C (F.cutoff w) (primorial w) (label u)).symm]
    exact harmonicDivisorMass_nonneg _ _ (hH u)
  have htρ (u : Fin q) : total (ρ u) = 1 := by
    rw [show ρ u = harmonicDivisorMass (fun j : C.tail (label u) => F.cutoff w j) (primorial w)
      from (harmonicDivisorMass_chain_tail C (F.cutoff w) (primorial w) (label u)).symm]
    exact harmonicDivisorMass_total _ _ (hH u)
  have hs (k : Fin q → ℕ) (hk : k ∈ (piMass ρ).support) (u : Fin q) :
      k u ≠ 0 ∧ k u ≤ V ∧ (k u).primeFactors ⊆ S := by
    have h := master_chain_divisor_support hF C w hN label (fun j hj => (hv j hj).1) hk u
    exact ⟨h.1.ne', h.2.1.trans (hdivbudget u), master_chain_divisor_primeFactors
      hF C w V hN label (fun j hj => (hv j hj).1) hdivbudget hk u⟩
  have hp := hF.prime_slots_squarefree_bound w gap S hS
    (fun p hp => ((mem_boundedRoughPrimeSet w V p).mp hp).2.1)
    (fun j p hp => ((mem_boundedRoughPrimeSet w V p).mp hp).2.2.trans (hprimebudget j))
  exact squarefree_weighted_integer_linear_forms_mean_one_error S hS ρ hρ htρ
    (masterPrimeSlotsMass F w gap) (hF.prime_slots_nonneg w gap) (hF.prime_slots_total w gap)
    base c E T (fun x j => (x j : ZMod (squarefreeCRTModulus S))) V εbase _ hεbase hs
    hprimitive (fun _k _hk x hx p _he => hindependent x hx p) hp
    (fun x hx k hk => hbase x hx k hk
      (Finset.prod_ne_zero_iff.mpr (fun u _ => (hs k hk u).1)))

theorem MasterParameterConditions.chain_weighted_mean_one_tendsto {n N m q r d L : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (C : ℕ → Chain m)
    (hN : ∀ w i, (C w).block i ⊆ Finset.range N) (label : ℕ → Fin q → Fin m)
    (gap : ℕ → Fin r → Fin L) (V : ℕ → ℕ) (hV : ∀ᶠ w in atTop, 1 ≤ V w)
    (hdivbudget : ∀ᶠ w in atTop, ∀ u, tailBound ((C w).tailCutoffs (F.cutoff w) (label w u)) ≤ V w)
    (hprimebudget : ∀ᶠ w in atTop, ∀ j, V w ≤ F.auxiliary w (gap w j))
    (T : Finset (MvPolynomial (Fin r) ℤ)) (hT : ∀ f ∈ T, f ≠ 0)
    (base : ℕ → (Fin r → ℕ) → Mass (Fin d → ℤ))
    (c : ℕ → (Fin r → ℕ) → Fin q → Fin d → ℤ) (E : ℕ → (Fin r → ℕ) → Prop)
    (εbase : ℕ → ℝ) (hεbase : ∀ᶠ w in atTop, 0 ≤ εbase w)
    (hεrapid : RapidlySmall atTop (fun w => (V w : ℝ)) εbase)
    (hprimitive : ∀ᶠ w in atTop, ∀ x, E w x → ∀ p : boundedRoughPrimeSet w (V w), ∀ u,
      ∃ j, (c w x u j : ZMod (p : ℕ)) ≠ 0)
    (hindependent : ∀ᶠ w in atTop, ∀ x, E w x → ∀ p : boundedRoughPrimeSet w (V w),
      ¬ squarefreeCRTBadEvent (boundedRoughPrimeSet w (V w))
        (fun p hp => ((mem_boundedRoughPrimeSet w (V w) p).mp hp).1) T
          (fun j => (x j : ZMod (squarefreeCRTModulus (boundedRoughPrimeSet w (V w))))) p →
        ∀ u v, u ≠ v → LinearIndependent (ZMod (p : ℕ))
          ![(fun j => (c w x u j : ZMod (p : ℕ))), (fun j => (c w x v j : ZMod (p : ℕ)))])
    (hbase : ∀ᶠ w in atTop, ∀ x, E w x →
      ∀ k ∈ (masterChainDivisorMass F w (C w) (label w)).support,
      ∀ hprod : (∏ u, k u) ≠ 0,
        letI : NeZero (∏ u, k u) := ⟨hprod⟩
        distance ((base w x).mapDomain (fun y j => (y j : ZMod (∏ u, k u))))
          (uniformFintypeMass (Fin d → ZMod (∏ u, k u))) ≤ εbase w) :
    Tendsto (fun w => masterChainWeightedMean F w (C w) (label w) (fun j => gap w j)
        (base w) (c w) (E w) - event (masterPrimeSlotsMass F w (fun j => gap w j)) (E w))
      atTop (𝓝 0) := by
  let S := fun w => boundedRoughPrimeSet w (V w)
  have hS : ∀ w, ∀ p ∈ S w, p.Prime :=
    fun w p hp => ((mem_boundedRoughPrimeSet w (V w) p).mp hp).1
  have hm := hF.chain_divisor_CRT_excess_tendsto_zero T hT C hN label S hS
    (fun w p hp => ((mem_boundedRoughPrimeSet w (V w) p).mp hp).2.1)
  have hp := hF.prime_slots_weighted_error_tendsto_zero gap hV hprimebudget q
  have hb : Tendsto (fun w => (V w : ℝ) ^ q * εbase w) atTop (𝓝 0) := by
    apply (isLittleO_one_iff ℝ).mp
    simpa only [pow_zero, inv_one] using (hεrapid.mul_power
      (hV.mono (fun _ hw => by exact_mod_cast (by omega : 0 < V _))) q) 0
  have ht : Tendsto (fun w => expectation (masterChainDivisorMass F w (C w) (label w))
      (comparisonPrimePowerCRTIntegrand (S w) (hS w) T) +
      ((V w : ℝ) ^ q * εbase w + (V w : ℝ) ^ q * masterPrimeSlotsResidueError F w (fun j => gap w j)))
      atTop (𝓝 0) := by
    simpa only [zero_add, masterChainDivisorMass] using hm.add (hb.add hp)
  have hbound : ∀ᶠ w in atTop,
      |masterChainWeightedMean F w (C w) (label w) (fun j => gap w j) (base w) (c w) (E w) -
        event (masterPrimeSlotsMass F w (fun j => gap w j)) (E w)| ≤
      expectation (masterChainDivisorMass F w (C w) (label w))
        (comparisonPrimePowerCRTIntegrand (S w) (hS w) T) +
      ((V w : ℝ) ^ q * εbase w + (V w : ℝ) ^ q * masterPrimeSlotsResidueError F w (fun j => gap w j)) := by
    filter_upwards [hF.raw_cutoffs_valid, hdivbudget, hprimebudget, hεbase, hprimitive, hindependent, hbase]
      with w hv hdiv hprime hε hprim hind hbasew
    have h := hF.chain_squarefree_weighted_error w (V w) (C w) (hN w) (label w) _
      (fun j hj => ⟨(hv j hj).1, (hv j hj).2.2⟩) hdiv hprime T (base w) (c w) (E w)
      (εbase w) hε hprim hind hbasew
    simpa only [Nat.cast_pow, mul_add] using h
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) hbound ht

end Hindman168
