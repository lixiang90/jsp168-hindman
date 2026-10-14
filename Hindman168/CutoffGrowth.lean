import Hindman168.PowerGrowth
import Hindman168.SamplingAsymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Constructive dyadic harmonic cutoffs and actual power domination

The paper chooses a power of two with log X >= w R^w. The cutoff below
is explicit. Its logarithm dominates every fixed power of a varying R
whenever R >= 1 eventually. No growth of the sampling errors is assumed.
This does not construct the prime pools or the full master-scale family.
-/

namespace Hindman168

open Filter Asymptotics
open scoped Topology

theorem powerDominates_of_parameter_power {F R : ℕ → ℝ}
    (hR : ∀ᶠ (w : ℕ) in atTop, 1 ≤ R w)
    (hF : ∀ᶠ (w : ℕ) in atTop, (w : ℝ) * R w ^ w ≤ F w) :
    PowerDominates atTop F R := by
  intro n
  apply isLittleO_iff.mpr
  intro c hc
  have ht : Tendsto (fun w : ℕ => (w : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop n, hR, hF, ht.eventually (eventually_ge_atTop (1 / c))]
    with w hwn hRw hFw hcw
  have hRpos : 0 < R w := lt_of_lt_of_le zero_lt_one hRw
  have hp : 0 ≤ R w ^ w := pow_nonneg hRpos.le w
  have hFnonneg : 0 ≤ F w := (mul_nonneg (Nat.cast_nonneg w) hp).trans hFw
  have hpow : R w ^ n ≤ R w ^ w := pow_le_pow_right₀ hRw hwn
  have hcW : (1 : ℝ) ≤ c * w := by
    have h := (div_le_iff₀ hc).mp hcw
    nlinarith
  simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hRpos.le n), abs_of_nonneg hFnonneg]
  calc
    _ ≤ R w ^ w := hpow
    _ ≤ c * ((w : ℝ) * R w ^ w) := by nlinarith
    _ ≤ c * F w := mul_le_mul_of_nonneg_left hFw hc.le

noncomputable def dyadicHarmonicCutoff (R w : ℕ) : ℕ :=
  2 ^ Nat.ceil ((w : ℝ) * (R : ℝ) ^ w / Real.log 2)

theorem dyadicHarmonicCutoff_log_lower (R w : ℕ) :
    (w : ℝ) * (R : ℝ) ^ w ≤ Real.log (dyadicHarmonicCutoff R w) := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hc := Nat.le_ceil ((w : ℝ) * (R : ℝ) ^ w / Real.log 2)
  unfold dyadicHarmonicCutoff
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  exact (div_le_iff₀ hlog).mp hc

theorem dyadicHarmonicCutoff_powerDominates {R : ℕ → ℕ}
    (hR : ∀ᶠ (w : ℕ) in atTop, 1 ≤ R w) :
    PowerDominates atTop (fun w => Real.log (dyadicHarmonicCutoff (R w) w))
      (fun w => (R w : ℝ)) :=
  powerDominates_of_parameter_power (R := fun w : ℕ => (R w : ℝ))
    (hR.mono (fun _ hw => by exact_mod_cast hw))
    (Eventually.of_forall (fun w => dyadicHarmonicCutoff_log_lower (R w) w))

theorem dyadicHarmonicCutoff_auxiliary_domination {R Q : ℕ → ℕ}
    (hR : ∀ᶠ w in atTop, 1 ≤ R w) (d : ℕ)
    (hQ : ∀ᶠ w in atTop, Q w ≤ R w ^ d) :
    PowerDominates atTop (fun w => Real.log (dyadicHarmonicCutoff (R w) w))
      (fun w => (Q w : ℝ)) := by
  apply (dyadicHarmonicCutoff_powerDominates hR).mono_base d
  filter_upwards [hQ] with w hw
  exact ⟨Nat.cast_nonneg _, Nat.cast_nonneg _, by exact_mod_cast hw⟩

/-- The explicit dyadic choice satisfies all three sampling rate conclusions
whenever the auxiliary budget is bounded by a fixed power of R. -/
theorem dyadic_sampling_rates {R W K H V : ℕ → ℕ}
    (hR : ∀ᶠ w in atTop, 1 ≤ R w) (d : ℕ)
    (hcap : ∀ᶠ w in atTop, samplingSize (W w) (K w) (H w) (V w) ≤ R w ^ d)
    (hK : ∀ᶠ w in atTop, 1 ≤ K w) (hV : ∀ᶠ w in atTop, 1 ≤ V w) :
    RapidlySmall atTop (fun w => (V w : ℝ))
        (fun w => residueError (dyadicHarmonicCutoff (R w) w) (W w) (K w)) ∧
      RapidlySmall atTop (fun w => (V w : ℝ))
        (fun w => translationError (dyadicHarmonicCutoff (R w) w) (W w) (H w)) ∧
      RapidlySmall atTop (fun w => (V w : ℝ))
        (fun w => dilationError (dyadicHarmonicCutoff (R w) w) (W w) (K w)) := by
  have hD := dyadicHarmonicCutoff_auxiliary_domination hR d hcap
  have hDX := powerDominates_log_to_cutoff hD
  have hcap0 : ∀ᶠ w in atTop, samplingSize (W w) (K w) 0 (V w) ≤ R w ^ d :=
    hcap.mono (fun w hw => by unfold samplingSize at hw ⊢; omega)
  have hD0 := dyadicHarmonicCutoff_auxiliary_domination hR d hcap0
  exact ⟨residueError_rapid hDX hV, translationError_rapid hDX hV, dilationError_rapid hD0 hK hV⟩

theorem dyadic_sampling_eventually_valid {R W K H V : ℕ → ℕ}
    (hR : ∀ᶠ w in atTop, 1 ≤ R w) (d : ℕ)
    (hcap : ∀ᶠ w in atTop, samplingSize (W w) (K w) (H w) (V w) ≤ R w ^ d)
    (hW : ∀ᶠ w in atTop, 0 < W w) :
    ∀ᶠ w in atTop, 2 ≤ dyadicHarmonicCutoff (R w) w ∧
      (W w : ℝ) / dyadicHarmonicCutoff (R w) w < Real.log (dyadicHarmonicCutoff (R w) w) ∧
      0 < harmonicNormalizer (dyadicHarmonicCutoff (R w) w) (W w) :=
  sampling_eventually_valid
    (powerDominates_log_to_cutoff (dyadicHarmonicCutoff_auxiliary_domination hR d hcap)) hW

end Hindman168
