import Hindman168.MixedBaseSampling
import Hindman168.PolynomialSamplingBudgets
import Hindman168.MasterWeightedMeanOne

/-!
# Actual master base laws at every supported divisor-product modulus

The harmonic coordinates use the original master cutoffs. Auxiliary
intervals may depend on the fresh prime parameters, with arbitrary
locations and lengths bounded below by their growth scale. The common
residue cap is V^q, not V. Neither residue equidistribution nor a rapid
base-error conclusion is an input to these results.
-/

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

theorem master_chain_divisor_product_budget {n N m q : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (C : Chain m) (w V : ℕ)
    (hN : ∀ i, C.block i ⊆ Finset.range N) (label : Fin q → Fin m)
    (hX : ∀ j ∈ Finset.range N, 2 ≤ F.cutoff w j)
    (hV : ∀ u, tailBound (C.tailCutoffs (F.cutoff w) (label u)) ≤ V)
    {k : Fin q → ℕ} (hk : k ∈ (masterChainDivisorMass F w C label).support) :
    0 < (∏ u, k u) ∧ (∏ u, k u) ≤ V ^ q ∧ (primorial w).Coprime (∏ u, k u) := by
  have hs (u : Fin q) := master_chain_divisor_support hF C w hN label hX hk u
  refine ⟨Finset.prod_pos (fun u _ => (hs u).1), ?_, ?_⟩
  · simpa only [Fin.prod_const] using
      Finset.prod_le_prod' (fun u (_ : u ∈ (Finset.univ : Finset (Fin q))) =>
        (hs u).2.1.trans (hV u))
  · exact Nat.coprime_prod_right_iff.mpr (fun u _ => (hs u).2.2.symm)

theorem MasterParameterConditions.indexed_mixed_base_residue_rapid {n N d : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (H : Finset (Fin d))
    (index : ℕ → Fin d → Fin N) (V : ℕ → ℕ) (q : ℕ) (Tmin : ℕ → Fin d → ℕ)
    (hV : ∀ᶠ w in atTop, 1 ≤ V w)
    (hbudget : ∀ᶠ w in atTop, ∀ j ∈ H, V w ≤ F.auxiliary w (index w j).val)
    (hT : ∀ j, j ∉ H → PowerDominates atTop (fun w => (Tmin w j : ℝ))
      (fun w => (samplingSize 0 (V w) 0 (V w) : ℝ))) :
    RapidlySmall atTop (fun w => (V w : ℝ))
      (fun w => mixedBaseResidueError H (fun j => F.cutoff w (index w j).val)
        (primorial w) (Tmin w) (V w ^ q)) := by
  apply mixedBaseResidueError_rapid
  · intro j hj
    exact powerDominates_log_to_cutoff (hF.indexed_product_sampling_growth
      (fun w => index w j) q (hbudget.mono (fun w hw => hw j hj)))
  · intro j hj
    exact (hT j hj).sampling_power_cap q
  · exact hV

theorem MasterParameterConditions.mixed_base_error_eventually_nonneg {n N d : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (H : Finset (Fin d))
    (index : ℕ → Fin d → Fin N) (Tmin : ℕ → Fin d → ℕ) (B : ℕ → ℕ) :
    ∀ᶠ w in atTop, 0 ≤ mixedBaseResidueError H (fun j => F.cutoff w (index w j).val)
      (primorial w) (Tmin w) (B w) := by
  filter_upwards [hF.raw_cutoffs_valid] with w hw
  apply mixedBaseResidueError_nonneg
  intro j _
  exact (hw (index w j).val (Finset.mem_range.mpr (index w j).isLt)).2.1

theorem MasterParameterConditions.chain_mixed_base_residue_bound {n N m q r d : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (C : ℕ → Chain m)
    (hN : ∀ w i, (C w).block i ⊆ Finset.range N) (label : ℕ → Fin q → Fin m)
    (H : Finset (Fin d)) (index : ℕ → Fin d → Fin N) (V : ℕ → ℕ)
    (Tmin : ℕ → Fin d → ℕ)
    (hdivbudget : ∀ᶠ w in atTop, ∀ u, tailBound ((C w).tailCutoffs (F.cutoff w) (label w u)) ≤ V w)
    (hT : ∀ j, j ∉ H → PowerDominates atTop (fun w => (Tmin w j : ℝ))
      (fun w => (samplingSize 0 (V w) 0 (V w) : ℝ)))
    (loc : ℕ → (Fin r → ℕ) → Fin d → ℤ)
    (len : ℕ → (Fin r → ℕ) → Fin d → ℕ) (E : ℕ → (Fin r → ℕ) → Prop)
    (hlen : ∀ᶠ w in atTop, ∀ x, E w x → ∀ j, j ∉ H → Tmin w j ≤ len w x j) :
    ∀ᶠ w in atTop, ∀ x, E w x →
      ∀ k ∈ (masterChainDivisorMass F w (C w) (label w)).support,
      ∀ hprod : (∏ u, k u) ≠ 0,
        letI : NeZero (∏ u, k u) := ⟨hprod⟩
        distance ((mixedIntegerBaseMass H (fun j => F.cutoff w (index w j).val)
          (primorial w) (loc w x) (len w x)).mapDomain
            (fun y : Fin d → ℤ => fun j => (y j : ZMod (∏ u, k u))))
          (uniformFintypeMass (Fin d → ZMod (∏ u, k u))) ≤
            mixedBaseResidueError H (fun j => F.cutoff w (index w j).val)
              (primorial w) (Tmin w) (V w ^ q) := by
  have hpos : ∀ᶠ w in atTop, ∀ j, j ∉ H → 0 < Tmin w j := by
    apply eventually_all.mpr
    intro j
    by_cases hj : j ∈ H
    · exact Eventually.of_forall (fun _ hn => False.elim (hn hj))
    · exact (uniform_interval_eventually_positive (hT j hj)).mono (fun _ hw _ => hw)
  filter_upwards [hF.raw_cutoffs_valid, hdivbudget, hlen, hpos] with w hw hd hl hp
  intro x hx k hk hprod
  letI : NeZero (∏ u, k u) := ⟨hprod⟩
  have hb := master_chain_divisor_product_budget hF (C w) w (V w) (hN w) (label w)
    (fun j hj => (hw j hj).1) hd hk
  exact mixed_integer_base_zmod_distance H _ _ (loc w x) (len w x) (Tmin w)
    (primorial_pos w) hb.2.2 hb.2.1
    (fun j _ => (hw (index w j).val (Finset.mem_range.mpr (index w j).isLt)).1)
    (fun j _ => (hw (index w j).val (Finset.mem_range.mpr (index w j).isLt)).2.1)
    (fun j hj => ⟨hp j hj, hl x hx j hj⟩)

end Hindman168
