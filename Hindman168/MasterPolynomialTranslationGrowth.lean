import Hindman168.MasterTranslationScales

/-! Actual varying master cutoffs dominate every fixed polynomial in an
ordered earlier gap. These growth statements supply the translation
sampling budget, rather than assuming a small total-variation error. -/

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical

theorem MasterParameterConditions.indexed_pool_auxiliary_le_gap
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (index : ℕ → Fin N) :
    ∀ᶠ w in atTop, (F.pool w (index w).val).upper + F.auxiliary w (index w).val ≤
      F.gap w (index w).val := by
  have hg := PowerDominates.finite_choice (fun i : Fin N => hF.gap_growth i.val) index
  filter_upwards [hg.eventually_bound (Eventually.of_forall (fun _ => Nat.cast_nonneg _))
    (Eventually.of_forall (fun _ => by positivity)) 1 (by norm_num : (0 : ℝ) < 1)] with w hw
  simp only [pow_one, one_mul] at hw
  exact_mod_cast hw

theorem MasterParameterConditions.indexed_gap_eventually_large
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (index : ℕ → Fin N) (K : ℕ) :
    ∀ᶠ w in atTop, K ≤ F.gap w (index w).val := by
  have hg := PowerDominates.finite_choice (fun i : Fin N => hF.gap_growth i.val) index
  filter_upwards [hg.eventually_bound (A := ((K + 1 : ℕ) : ℝ))
    (Eventually.of_forall (fun _ => Nat.cast_nonneg _))
    (Eventually.of_forall (fun _ => by positivity)) 0 (by positivity)] with w hw
  simp only [pow_zero, mul_one] at hw
  have hn : K + 1 ≤ F.gap w (index w).val := by exact_mod_cast hw
  omega

theorem MasterParameterConditions.polynomial_gap_sampling_growth
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (index : ℕ → Fin N) (K q : ℕ)
    {H V : ℕ → ℕ}
    (hH : ∀ᶠ w in atTop, H w ≤ K * F.gap w (index w).val ^ q)
    (hV : ∀ᶠ w in atTop, V w ≤ F.auxiliary w (index w).val) :
    PowerDominates atTop (fun w => (F.cutoff w (index w).val : ℝ))
      (fun w => (samplingSize (primorial w) 0 (H w) (V w) : ℝ)) := by
  apply (powerDominates_log_to_cutoff (hF.indexed_cutoff_gap_growth index)).mono_base (q + 2)
  filter_upwards [hF.indexed_gap_eventually_large index (K + 4),
    hF.primorial_le_modulus, hF.auxiliary_le_gap_eventually index, hH, hV]
    with w hlarge hWw haw hHw hVw
  let R := F.gap w (index w).val
  have hR : 4 ≤ R := by dsimp [R]; omega
  have hK : K ≤ R := by dsimp [R]; omega
  have hW : primorial w ≤ R := hWw.trans ((F.modulus_le_auxiliary _ _).trans haw)
  have hv : V w ≤ R := hVw.trans haw
  have hp : 1 ≤ R ^ q := one_le_pow₀ (by omega)
  have hRpow : R ≤ R ^ (q + 1) := by
    simpa only [pow_succ, one_mul] using Nat.mul_le_mul_right R hp
  have hHpow : H w ≤ R ^ (q + 1) := by
    exact hHw.trans (by simpa only [pow_succ, Nat.mul_comm] using Nat.mul_le_mul_right (R ^ q) hK)
  have hs : samplingSize (primorial w) 0 (H w) (V w) ≤ 4 * R ^ (q + 1) := by
    unfold samplingSize
    omega
  have hb : 4 * R ^ (q + 1) ≤ R ^ (q + 2) := by
    simpa only [show q + 2 = (q + 1) + 1 by omega, pow_succ, Nat.mul_comm] using
      Nat.mul_le_mul_right (R ^ (q + 1)) hR
  exact ⟨Nat.cast_nonneg _, Nat.cast_nonneg _, by exact_mod_cast hs.trans hb⟩

theorem MasterParameterConditions.earlier_polynomial_translation_growth
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (gap pivot : ℕ → Fin N) (K q : ℕ)
    (horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val) :
    PowerDominates atTop (fun w => (F.cutoff w (pivot w).val : ℝ))
      (fun w => (samplingSize (primorial w) 0
        (K * F.gap w (gap w).val *
          ((F.pool w (gap w).val).upper + F.auxiliary w (gap w).val) ^ q)
        (F.auxiliary w (gap w).val) : ℝ)) := by
  apply hF.polynomial_gap_sampling_growth pivot K (q + 1)
  · filter_upwards [hF.indexed_pool_auxiliary_le_gap gap, horder] with w hw ho
    have hR := hF.gap_monotone w ho
    have hh := Nat.mul_le_mul_left (F.gap w (gap w).val) (Nat.pow_le_pow_left hw q)
    have he : F.gap w (gap w).val *
        ((F.pool w (gap w).val).upper + F.auxiliary w (gap w).val) ^ q ≤
        F.gap w (pivot w).val ^ (q + 1) := by
      calc
        _ ≤ F.gap w (gap w).val * F.gap w (gap w).val ^ q := hh
        _ = F.gap w (gap w).val ^ (q + 1) := by rw [pow_succ, Nat.mul_comm]
        _ ≤ _ := Nat.pow_le_pow_left hR _
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left K he
  · exact horder.mono (fun w hw => hF.auxiliary_monotone w hw)

end Hindman168
