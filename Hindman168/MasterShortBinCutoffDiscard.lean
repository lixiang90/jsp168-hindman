import Hindman168.ShortBinCutoffProbability
import Hindman168.MasterShortCubeRemainder
import Hindman168.MasterDivisorSampling
import Mathlib.Data.Nat.Sqrt

/-! The cutoff-bin discard vanishes for the actual master cutoffs and
roughness moduli. Any nonnegative width bounded by the pivot gap works,
including the modulus-aligned integer square-root microcell width. -/

namespace Hindman168

open FiniteMass Filter
open scoped Topology Classical

theorem master_failedCutoffShortBin_tendsto
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (pivot : ℕ → Fin N)
    (R tlo : ℕ → ℝ) {C : ℝ} (hC : 1 ≤ C)
    (hR : ∀ᶠ w in atTop, 0 ≤ R w ∧ R w ≤ F.gap w (pivot w).val)
    (htlo : ∀ᶠ w in atTop, 0 < tlo w) :
    Tendsto (fun w => event (rawMass (F.cutoff w (pivot w).val) (primorial w))
      (failedCutoffShortBin (F.cutoff w (pivot w).val) (R w) (tlo w) C)) atTop (𝓝 0) := by
  have hX : Tendsto (fun w => (F.cutoff w (pivot w).val : ℝ)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    have hh : ∀ᶠ w in atTop, ∀ i : Fin N, b ≤ (F.cutoff w i.val : ℝ) :=
      eventually_all.mpr (fun i =>
        (tendsto_natCast_atTop_atTop.comp (hF.cutoff_tendsto i.val)).eventually (eventually_ge_atTop b))
    exact hh.mono (fun w hw => hw (pivot w))
  have hgap := hF.cell_width_cutoff_ratio_tendsto pivot pivot (Eventually.of_forall (fun _ => le_rfl))
  have hWX : Tendsto (fun w => (primorial w : ℝ) / F.cutoff w (pivot w).val) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _ hgap
    filter_upwards [hF.primorial_le_modulus, hF.auxiliary_le_gap_eventually pivot] with w hw hg
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast hw.trans ((F.modulus_le_auxiliary w (pivot w).val).trans hg)
  have hRX : Tendsto (fun w => R w / F.cutoff w (pivot w).val) atTop (𝓝 0) :=
    squeeze_zero' (hR.mono (fun w hw => div_nonneg hw.1 (Nat.cast_nonneg _)))
      (hR.mono (fun w hw => div_le_div_of_nonneg_right hw.2 (Nat.cast_nonneg _))) hgap
  exact rawMass_failedCutoffShortBin_tendsto _ _ R tlo hC hX hWX hRX
    (Eventually.of_forall primorial_pos) (hR.mono (fun _ hw => hw.1)) htlo

theorem alignedSqrtWidth_le (H M : ℕ) : M * (Nat.sqrt H / M) ≤ H :=
  (Nat.mul_div_le (Nat.sqrt H) M).trans (Nat.sqrt_le_self H)

theorem master_alignedSqrt_failedCutoffShortBin_tendsto
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (pivot : ℕ → Fin N)
    (M : ℕ → ℕ) (tlo : ℕ → ℝ) {C : ℝ} (hC : 1 ≤ C)
    (htlo : ∀ᶠ w in atTop, 0 < tlo w) :
    Tendsto (fun w => event (rawMass (F.cutoff w (pivot w).val) (primorial w))
      (failedCutoffShortBin (F.cutoff w (pivot w).val)
        ((M w * (Nat.sqrt (F.gap w (pivot w).val) / M w) : ℕ) : ℝ) (tlo w) C)) atTop (𝓝 0) := by
  apply master_failedCutoffShortBin_tendsto hF pivot _ tlo hC _ htlo
  exact Eventually.of_forall (fun w => ⟨Nat.cast_nonneg _, by
    exact_mod_cast alignedSqrtWidth_le (F.gap w (pivot w).val) (M w)⟩)

end Hindman168
