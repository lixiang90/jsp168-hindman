import Hindman168.MasterPolynomialTranslationGrowth

/-! Logarithmic master growth absorbs affine sampling budgets of any fixed
polynomial degree. No small-error hypothesis is used here. -/

namespace Hindman168

open Filter Asymptotics
open scoped Topology Classical

theorem MasterParameterConditions.polynomial_gap_affine_log_growth
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (index : ℕ → Fin N) (L q : ℕ)
    {K H V : ℕ → ℕ}
    (hK : ∀ᶠ w in atTop, K w ≤ L * F.gap w (index w).val ^ q)
    (hH : ∀ᶠ w in atTop, H w ≤ L * F.gap w (index w).val ^ q)
    (hV : ∀ᶠ w in atTop, V w ≤ F.auxiliary w (index w).val) :
    PowerDominates atTop (fun w => Real.log (F.cutoff w (index w).val : ℝ))
      (fun w => (samplingSize (primorial w) (K w) (H w) (V w) : ℝ)) := by
  apply (hF.indexed_cutoff_gap_growth index).mono_base (q + 2)
  filter_upwards [hF.indexed_gap_eventually_large index (L + 5), hF.primorial_le_modulus,
    hF.auxiliary_le_gap_eventually index, hK, hH, hV] with w hlarge hWw haw hKw hHw hVw
  let R := F.gap w (index w).val
  have hR : 5 ≤ R := by dsimp [R]; omega
  have hL : L ≤ R := by dsimp [R]; omega
  have hW : primorial w ≤ R := hWw.trans ((F.modulus_le_auxiliary _ _).trans haw)
  have hv : V w ≤ R := hVw.trans haw
  have hp : 1 ≤ R ^ q := one_le_pow₀ (by omega)
  have hRp : R ≤ R ^ (q + 1) := by
    simpa only [pow_succ, one_mul] using Nat.mul_le_mul_right R hp
  have hkp : K w ≤ R ^ (q + 1) := hKw.trans
    (by simpa only [pow_succ, Nat.mul_comm] using Nat.mul_le_mul_right (R ^ q) hL)
  have hhp : H w ≤ R ^ (q + 1) := hHw.trans
    (by simpa only [pow_succ, Nat.mul_comm] using Nat.mul_le_mul_right (R ^ q) hL)
  have hs : samplingSize (primorial w) (K w) (H w) (V w) ≤ 5 * R ^ (q + 1) := by
    unfold samplingSize
    omega
  have hb : 5 * R ^ (q + 1) ≤ R ^ (q + 2) := by
    simpa only [show q + 2 = (q + 1) + 1 by omega, pow_succ, Nat.mul_comm] using
      Nat.mul_le_mul_right (R ^ (q + 1)) hR
  exact ⟨Nat.cast_nonneg _, Nat.cast_nonneg _, by exact_mod_cast hs.trans hb⟩

theorem MasterParameterConditions.earlier_pool_power_affine_log_growth
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (gap pivot : ℕ → Fin N) (q : ℕ)
    (horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val) :
    PowerDominates atTop (fun w => Real.log (F.cutoff w (pivot w).val : ℝ))
      (fun w => (samplingSize (primorial w)
        (((F.pool w (gap w).val).upper + F.auxiliary w (gap w).val) ^ q) 0
        (F.auxiliary w (gap w).val) : ℝ)) := by
  apply hF.polynomial_gap_affine_log_growth pivot 1 q
  · filter_upwards [hF.indexed_pool_auxiliary_le_gap gap, horder] with w hw ho
    simpa only [one_mul] using Nat.pow_le_pow_left (hw.trans (hF.gap_monotone w ho)) q
  · exact Eventually.of_forall (fun _ => Nat.zero_le _)
  · exact horder.mono (fun w hw => hF.auxiliary_monotone w hw)

end Hindman168
