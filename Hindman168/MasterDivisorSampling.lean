import Hindman168.FreshDivisorOccurrences
import Hindman168.MasterSamplingBudgets
import Hindman168.BoundedDivisorCRT

/-!
# Actual master cutoffs and independently sampled tail divisors

The normalizer and comparison hypotheses follow from the original master
growth conditions. A chain inside the finite master index set supplies the
uniform row-arity bound. Its actual fresh occurrence law has positive,
rough divisors bounded by their actual tail product, even when
block labels repeat.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

theorem MasterParameterConditions.cutoff_tendsto {n N : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (j : ℕ) :
    Tendsto (fun w => F.cutoff w j) atTop atTop := by
  apply tendsto_atTop.2
  intro B
  have hg := powerDominates_log_to_cutoff (hF.cutoff_auxiliary_growth j)
  have he := hg.eventually_bound
    (Eventually.of_forall (fun w => Nat.cast_nonneg (F.cutoff w j)))
    (Eventually.of_forall (fun w => Nat.cast_nonneg (F.auxiliary w j)))
    0 (by positivity : (0 : ℝ) < (B : ℝ) + 1)
  filter_upwards [he] with w hw
  simp only [pow_zero, mul_one] at hw
  have hb : (B : ℝ) ≤ F.cutoff w j := by linarith
  exact_mod_cast hb

theorem MasterParameterConditions.raw_comparison_cutoffs {n N : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) :
    ∀ᶠ w in atTop, ∀ j ∈ Finset.range N,
      2 ≤ F.cutoff w j ∧ primorial w ≤ F.cutoff w j ∧
        0 < harmonicNormalizer (F.cutoff w j) (primorial w) ∧
        2 ≤ Real.log (F.cutoff w j : ℝ) ∧
        powerUnitNormalizer (comparisonExponent (F.cutoff w j)) 1 ≤
          2 * Real.log (F.cutoff w j : ℝ) := by
  apply (eventually_all_finset (Finset.range N)).mpr
  intro j hj
  have hg := hF.sampling_budget_growth j (K := fun _ => 0) (H := fun _ => 0) (V := fun _ => 1)
    (Eventually.of_forall (fun _ => Nat.zero_le _))
    (Eventually.of_forall (fun _ => Nat.zero_le _))
    (Eventually.of_forall (fun w => by have h := F.auxiliary_ge_two w j; omega))
  have ht := hF.cutoff_tendsto j
  have hl := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp ht)).eventually
    (eventually_ge_atTop (2 : ℝ))
  filter_upwards [hF.raw_cutoffs_valid,
    sampling_eventually_geometry (powerDominates_log_to_cutoff hg), hl,
    ht.eventually powerUnitNormalizer_comparison_eventually_le] with w hv hgeom hlog hZ
  exact ⟨(hv j hj).1, by omega, (hv j hj).2.2, hlog, hZ⟩

theorem chain_tail_raw_count_le {m N : ℕ} (C : Chain m)
    (hN : ∀ i, C.block i ⊆ Finset.range N) (i : Fin m) :
    Fintype.card (C.tail i) ≤ N := by
  have ht : C.tail i ⊆ Finset.range N := fun j hj =>
    hN i (Finset.mem_insert_of_mem hj)
  simpa only [Fintype.card_coe, Finset.card_range] using Finset.card_le_card ht

theorem chain_occurrences_raw_count_le {m q N : ℕ} (C : Chain m)
    (hN : ∀ i, C.block i ⊆ Finset.range N) (label : Fin q → Fin m) :
    (∑ i, Fintype.card (C.tail (label i))) ≤ N * q :=
  variable_raw_count_le N (fun i => chain_tail_raw_count_le C hN (label i))

theorem chain_divisor_support_actual_tail {m q N : ℕ} (C : Chain m)
    (X : ℕ → ℕ) (W : ℕ) (hN : ∀ i, C.block i ⊆ Finset.range N)
    (label : Fin q → Fin m) (hX : ∀ j ∈ Finset.range N, 2 ≤ X j) {k : Fin q → ℕ}
    (hk : k ∈ (FiniteMass.piMass (fun i => tailMass W (C.tailCutoffs X (label i)))).support)
    (i : Fin q) :
    0 < k i ∧ k i ≤ tailBound (C.tailCutoffs X (label i)) ∧ (k i).Coprime W := by
  have hm : k ∈ (variableHarmonicRowDivisorMass
      (fun (i : Fin q) (j : C.tail (label i)) => X j) W).support := by
    simpa only [variableHarmonicRowDivisorMass, harmonicDivisorMass_chain_tail] using hk
  have hs := variableHarmonicRowDivisorMass_support
    (fun (i : Fin q) (j : C.tail (label i)) => X j) W
    (fun i j => hX j (hN (label i) (Finset.mem_insert_of_mem j.property))) hm i
  have hp : (∏ j : C.tail (label i), X j ^ 2) = tailBound (C.tailCutoffs X (label i)) := by
    rw [chain_tailBound_eq]
    exact Finset.prod_coe_sort (C.tail (label i)) (fun j => X j ^ 2)
  exact ⟨hs.1, hs.2.1.trans hp.le, hs.2.2⟩


theorem master_chain_divisor_support {n N m q : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (_hF : MasterParameterConditions N A D F) (C : Chain m) (w : ℕ)
    (hN : ∀ i, C.block i ⊆ Finset.range N) (label : Fin q → Fin m)
    (hX : ∀ j ∈ Finset.range N, 2 ≤ F.cutoff w j) {k : Fin q → ℕ}
    (hk : k ∈ (piMass (fun i => tailMass (primorial w)
      (C.tailCutoffs (F.cutoff w) (label i)))).support) (i : Fin q) :
    0 < k i ∧ k i ≤ tailBound (C.tailCutoffs (F.cutoff w) (label i)) ∧ (k i).Coprime (primorial w) := by
  exact chain_divisor_support_actual_tail C (F.cutoff w) (primorial w) hN label hX hk i

theorem master_chain_divisor_primeFactors {n N m q : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (C : Chain m) (w V : ℕ)
    (hN : ∀ i, C.block i ⊆ Finset.range N) (label : Fin q → Fin m)
    (hX : ∀ j ∈ Finset.range N, 2 ≤ F.cutoff w j)
    (hV : ∀ i, tailBound (C.tailCutoffs (F.cutoff w) (label i)) ≤ V) {k : Fin q → ℕ}
    (hk : k ∈ (piMass (fun i => tailMass (primorial w)
      (C.tailCutoffs (F.cutoff w) (label i)))).support) (i : Fin q) :
    (k i).primeFactors ⊆ boundedRoughPrimeSet w V := by
  have hs := master_chain_divisor_support hF C w hN label hX hk i
  exact bounded_unit_primeFactors_subset w V (primorial w) (k i)
    (hs.2.1.trans (hV i)) hs.2.2 (fun p hp hle => hp.dvd_primorial_iff.mpr hle)

end Hindman168
