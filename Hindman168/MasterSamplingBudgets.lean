import Hindman168.MasterParameterFamily
import Hindman168.JointSamplingAsymptotics

/-!
# Actual master cutoffs supply the harmonic sampling hypotheses

Every earlier tail-product bound is at most the full earlier-cutoff
product in V_l. Dyadic cutoffs are positive even before the asymptotic
range. Polynomial domination of the gaps and log cutoffs therefore
supplies the complete sampling budget and every finite raw normalization.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical

theorem MasterParameterFamily.auxiliary_ge_two (F : MasterParameterFamily) (w l : ℕ) :
    2 ≤ F.auxiliary w l := by unfold MasterParameterFamily.auxiliary; omega

theorem MasterParameterFamily.modulus_le_auxiliary (F : MasterParameterFamily) (w l : ℕ) :
    (F.modulus w : ℕ) ≤ F.auxiliary w l := by unfold MasterParameterFamily.auxiliary; omega

theorem MasterParameterConditions.cutoff_positive {n N : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (w j : ℕ) : 0 < F.cutoff w j := by
  obtain ⟨e, he⟩ := hF.dyadic_cutoff w j
  rw [he]
  exact Nat.pow_pos (by norm_num)

theorem MasterParameterConditions.primorial_le_modulus {n N : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) :
    ∀ᶠ w in atTop, primorial w ≤ (F.modulus w : ℕ) := by
  filter_upwards [eventually_ge_atTop 1] with w hw
  have hd : primorial w ∣ (primorial w) ^ w := by
    simpa only [pow_one] using pow_dvd_pow (primorial w) hw
  exact Nat.le_of_dvd (F.modulus w).pos (hd.trans (hF.primorial_power_dvd w))

theorem MasterParameterConditions.earlier_tail_product_bound {n N : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (w j : ℕ) (T : Finset ℕ)
    (hT : T ⊆ Finset.range j) : (∏ k ∈ T, F.cutoff w k ^ 2) ≤ F.auxiliary w j := by
  have hp : (∏ k ∈ T, F.cutoff w k ^ 2) ≤ ∏ k ∈ Finset.range j, F.cutoff w k ^ 2 :=
    Finset.prod_le_prod_of_subset_of_one_le' hT (fun k _ _ =>
      one_le_pow₀ (hF.cutoff_positive w k))
  unfold MasterParameterFamily.auxiliary
  omega

theorem MasterParameterConditions.auxiliary_monotone {n N : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (w : ℕ) : Monotone (F.auxiliary w) := by
  intro i j hij
  have hp : (∏ k ∈ Finset.range i, F.cutoff w k ^ 2) ≤ ∏ k ∈ Finset.range j, F.cutoff w k ^ 2 :=
    Finset.prod_le_prod_of_subset_of_one_le' (Finset.range_mono hij) (fun k _ _ =>
      one_le_pow₀ (hF.cutoff_positive w k))
  unfold MasterParameterFamily.auxiliary
  omega

theorem MasterParameterConditions.cutoff_auxiliary_growth {n N : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (j : ℕ) :
    PowerDominates atTop (fun w => Real.log (F.cutoff w j : ℝ))
      (fun w => (F.auxiliary w j : ℝ)) := by
  have hg := (hF.gap_growth j).eventually_bound
    (Eventually.of_forall (fun w => (Nat.cast_nonneg (F.gap w j) : (0 : ℝ) ≤ F.gap w j)))
    (Eventually.of_forall (fun w => by positivity)) 1 (by norm_num : (0 : ℝ) < 1)
  apply (hF.cutoff_growth j).mono_base 1
  filter_upwards [hg] with w hw
  simp only [pow_one, one_mul] at hw ⊢
  refine ⟨Nat.cast_nonneg _, Nat.cast_nonneg _, ?_⟩
  exact (le_add_of_nonneg_left (Nat.cast_nonneg (F.pool w j).upper)).trans hw

theorem MasterParameterConditions.sampling_budget_growth {n N : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (j : ℕ) {K H V : ℕ → ℕ}
    (hK : ∀ᶠ w in atTop, K w ≤ F.auxiliary w j)
    (hH : ∀ᶠ w in atTop, H w ≤ F.auxiliary w j)
    (hV : ∀ᶠ w in atTop, V w ≤ F.auxiliary w j) :
    PowerDominates atTop (fun w => Real.log (F.cutoff w j : ℝ))
      (fun w => (samplingSize (primorial w) (K w) (H w) (V w) : ℝ)) := by
  apply (hF.cutoff_auxiliary_growth j).mono_base 4
  filter_upwards [hF.primorial_le_modulus, hK, hH, hV] with w hWw hKw hHw hVw
  have hW : primorial w ≤ F.auxiliary w j := hWw.trans (F.modulus_le_auxiliary w j)
  have ha : (2 : ℝ) ≤ F.auxiliary w j := by exact_mod_cast F.auxiliary_ge_two w j
  have hs : samplingSize (primorial w) (K w) (H w) (V w) ≤ 2 + 4 * F.auxiliary w j := by
    unfold samplingSize
    omega
  have hsr : (samplingSize (primorial w) (K w) (H w) (V w) : ℝ) ≤ 5 * (F.auxiliary w j : ℝ) := by
    have hs' : (samplingSize (primorial w) (K w) (H w) (V w) : ℝ) ≤ 2 + 4 * (F.auxiliary w j : ℝ) := by
      exact_mod_cast hs
    linarith
  have hp : (5 : ℝ) ≤ (F.auxiliary w j : ℝ) ^ 3 := by
    calc
      (5 : ℝ) ≤ 2 ^ 3 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) ha 3
  have hm : 5 * (F.auxiliary w j : ℝ) ≤ (F.auxiliary w j : ℝ) ^ 4 := by
    simpa only [pow_succ] using mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (F.auxiliary w j))
  exact ⟨Nat.cast_nonneg _, Nat.cast_nonneg _, hsr.trans hm⟩

theorem MasterParameterConditions.raw_cutoffs_valid {n N : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) :
    ∀ᶠ w in atTop, ∀ j ∈ Finset.range N,
      2 ≤ F.cutoff w j ∧ (primorial w : ℝ) / F.cutoff w j < Real.log (F.cutoff w j : ℝ) ∧
        0 < harmonicNormalizer (F.cutoff w j) (primorial w) := by
  apply (eventually_all_finset (Finset.range N)).mpr
  intro j _
  have hg := hF.sampling_budget_growth j (K := fun _ => 0) (H := fun _ => 0) (V := fun _ => 1)
    (Eventually.of_forall (fun _ => Nat.zero_le _))
    (Eventually.of_forall (fun _ => Nat.zero_le _))
    (Eventually.of_forall (fun w => by have h := F.auxiliary_ge_two w j; omega))
  exact sampling_eventually_valid (powerDominates_log_to_cutoff hg)
    (Eventually.of_forall primorial_pos)

theorem chain_tailBound_eq {m : ℕ} (C : Chain m) (X : ℕ → ℕ) (i : Fin m) :
    tailBound (C.tailCutoffs X i) = ∏ j ∈ C.tail i, X j ^ 2 := by
  unfold tailBound Chain.tailCutoffs
  rw [List.map_ofFn, List.prod_ofFn]
  have h := Fintype.prod_equiv ((C.tail i).orderIsoOfFin rfl).toEquiv
    (fun k => X ((C.tail i).orderIsoOfFin rfl k) ^ 2)
    (fun j : C.tail i => X j.val ^ 2) (fun _ => rfl)
  exact h.trans (Finset.prod_coe_sort (C.tail i) (fun j => X j ^ 2))

theorem MasterParameterConditions.chain_tail_budget {n N m : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (C : Chain m) (w : ℕ) (i : Fin m) :
    tailBound (C.tailCutoffs (F.cutoff w) i) ≤ F.auxiliary w (C.pivot i) := by
  rw [chain_tailBound_eq]
  apply hF.earlier_tail_product_bound
  intro j hj
  exact Finset.mem_range.mpr (C.tails_before_pivots i i j hj)

theorem chain_tailCutoffs_valid {m N : ℕ} (C : Chain m) (X : ℕ → ℕ) (W : ℕ)
    (hN : ∀ i, C.block i ⊆ Finset.range N)
    (hv : ∀ j ∈ Finset.range N, 2 ≤ X j ∧ (W : ℝ) / X j < Real.log (X j : ℝ))
    (i : Fin m) : ValidCutoffs (C.tailCutoffs X i) W := by
  intro x hx
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
  exact hv _ (hN i (Finset.mem_insert_of_mem (((C.tail i).orderIsoOfFin rfl j).property)))

end Hindman168
