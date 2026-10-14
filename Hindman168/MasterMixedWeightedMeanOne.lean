import Hindman168.MasterBaseSampling

/-!
# Master weighted mean-one with the original mixed base laws

The base residue error is derived from actual harmonic cutoffs and auxiliary
interval lengths. No base residue-error or equidistribution conclusion is
assumed. The application-specific integer rows and their prime tests remain
explicit, together with the original divisor, prime-slot and harmonic budgets.
-/

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def masterMixedBaseMass {N d r : ℕ} (H : Finset (Fin d))
    (F : MasterParameterFamily) (index : ℕ → Fin d → Fin N)
    (loc : ℕ → (Fin r → ℕ) → Fin d → ℤ)
    (len : ℕ → (Fin r → ℕ) → Fin d → ℕ)
    (w : ℕ) (x : Fin r → ℕ) : Mass (Fin d → ℤ) :=
  mixedIntegerBaseMass H (fun j => F.cutoff w (index w j).val)
    (primorial w) (loc w x) (len w x)

theorem MasterParameterConditions.mixed_base_probability_on_event {n N d r : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (H : Finset (Fin d))
    (index : ℕ → Fin d → Fin N) (Tmin : ℕ → Fin d → ℕ) (V : ℕ → ℕ)
    (loc : ℕ → (Fin r → ℕ) → Fin d → ℤ)
    (len : ℕ → (Fin r → ℕ) → Fin d → ℕ) (E : ℕ → (Fin r → ℕ) → Prop)
    (hT : ∀ j, j ∉ H → PowerDominates atTop (fun w => (Tmin w j : ℝ))
      (fun w => (samplingSize 0 (V w) 0 (V w) : ℝ)))
    (hlen : ∀ᶠ w in atTop, ∀ x, E w x → ∀ j, j ∉ H → Tmin w j ≤ len w x j) :
    ∀ᶠ w in atTop, ∀ x, E w x →
      (∀ y, 0 ≤ masterMixedBaseMass H F index loc len w x y) ∧
        total (masterMixedBaseMass H F index loc len w x) = 1 := by
  have hpos : ∀ᶠ w in atTop, ∀ j, j ∉ H → 0 < Tmin w j := by
    apply eventually_all.mpr
    intro j
    by_cases hj : j ∈ H
    · exact Eventually.of_forall (fun _ hn => False.elim (hn hj))
    · exact (uniform_interval_eventually_positive (hT j hj)).mono (fun _ hw _ => hw)
  filter_upwards [hF.raw_cutoffs_valid, hlen, hpos] with w hw hl hp
  intro x hx
  have hH (j : Fin d) (_ : j ∈ H) :
      0 < harmonicNormalizer (F.cutoff w (index w j).val) (primorial w) :=
    (hw (index w j).val (Finset.mem_range.mpr (index w j).isLt)).2.2
  exact ⟨mixedIntegerBaseMass_nonneg H _ _ (loc w x) (len w x) hH,
    mixedIntegerBaseMass_total H _ _ (loc w x) (len w x) hH
      (fun j hj => lt_of_lt_of_le (hp j hj) (hl x hx j hj))⟩

theorem MasterParameterConditions.chain_mixed_weighted_mean_one_tendsto {n N m q r d L : ℕ}
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
    (c : ℕ → (Fin r → ℕ) → Fin q → Fin d → ℤ) (E : ℕ → (Fin r → ℕ) → Prop)
    (hharmbudget : ∀ᶠ w in atTop, ∀ j ∈ H, V w ≤ F.auxiliary w (index w j).val)
    (hlengthgrowth : ∀ j, j ∉ H → PowerDominates atTop (fun w => (Tmin w j : ℝ))
      (fun w => (samplingSize 0 (V w) 0 (V w) : ℝ)))
    (hlen : ∀ᶠ w in atTop, ∀ x, E w x → ∀ j, j ∉ H → Tmin w j ≤ len w x j)
    (hprimitive : ∀ᶠ w in atTop, ∀ x, E w x → ∀ p : boundedRoughPrimeSet w (V w), ∀ u,
      ∃ j, (c w x u j : ZMod (p : ℕ)) ≠ 0)
    (hindependent : ∀ᶠ w in atTop, ∀ x, E w x → ∀ p : boundedRoughPrimeSet w (V w),
      ¬ squarefreeCRTBadEvent (boundedRoughPrimeSet w (V w))
        (fun p hp => ((mem_boundedRoughPrimeSet w (V w) p).mp hp).1) T
          (fun j => (x j : ZMod (squarefreeCRTModulus (boundedRoughPrimeSet w (V w))))) p →
        ∀ u v, u ≠ v → LinearIndependent (ZMod (p : ℕ))
          ![(fun j => (c w x u j : ZMod (p : ℕ))), (fun j => (c w x v j : ZMod (p : ℕ)))]) :
    Tendsto (fun w => masterChainWeightedMean F w (C w) (label w) (fun j => gap w j)
        (masterMixedBaseMass H F index loc len w) (c w) (E w) - event (masterPrimeSlotsMass F w (fun j => gap w j)) (E w))
      atTop (𝓝 0) := by
  exact hF.chain_weighted_mean_one_tendsto C hN label gap V hV hdivbudget hprimebudget
    T hT (masterMixedBaseMass H F index loc len) c E
    (fun w => mixedBaseResidueError H (fun j => F.cutoff w (index w j).val)
      (primorial w) (Tmin w) (V w ^ q))
    (hF.mixed_base_error_eventually_nonneg H index Tmin (fun w => V w ^ q))
    (hF.indexed_mixed_base_residue_rapid H index V q Tmin hV hharmbudget hlengthgrowth)
    hprimitive hindependent
    (hF.chain_mixed_base_residue_bound C hN label H index V Tmin hdivbudget
      hlengthgrowth loc len E hlen)

end Hindman168
