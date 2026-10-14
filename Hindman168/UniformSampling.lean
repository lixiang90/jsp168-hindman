import Hindman168.SamplingAsymptotics
import Hindman168.FiniteTensor

/-!
# Uniform little-o conclusions for the actual harmonic sampling laws

The rates proved in SamplingAsymptotics depend only on the caps K and H.
Any varying admissible modulus, residue or signed shift is controlled by
those same rates. Weighted real test functions may lose any fixed power
of V. Original laws are probabilities; comparisons need not be normalized.
-/

namespace Hindman168

open Filter Asymptotics
open scoped Topology BigOperators

theorem harmonic_residue_class_rapid {α : Type*} {l : Filter α}
    {X W K H V k a : α → ℕ}
    (hD : PowerDominates l (fun w => (X w : ℝ))
      (fun w => (samplingSize (W w) (K w) (H w) (V w) : ℝ)))
    (hV : ∀ᶠ w in l, 1 ≤ V w)
    (hg : ∀ᶠ w in l, 0 < W w ∧ 0 < k w ∧ k w ≤ K w ∧
      (W w).Coprime (k w) ∧ a w < k w) :
    RapidlySmall l (fun w => (V w : ℝ))
      (fun w => (k w : ℝ) * residueProbability (X w) (W w) (k w) (a w) - 1) := by
  apply (residueError_rapid hD hV).of_abs_le
  filter_upwards [sampling_eventually_geometry hD, hg] with w hw hgw
  have hx : 2 ≤ X w := by omega
  have hl := sampling_denominator_pos hw.1 hw.2.1
  have hb := samplingSize_bounds (W w) (K w) (H w) (V w)
  have hc := residueError_polynomial (K := K w)
    (Q := (samplingSize (W w) (K w) (H w) (V w) : ℝ)) hw.1 hw.2.1
    (by exact_mod_cast hb.1) (by exact_mod_cast hb.2.1) (by exact_mod_cast hb.2.2.1)
  rw [abs_of_nonneg hc.1]
  exact (harmonic_residue_error hx hgw.1 hgw.2.1 hgw.2.2.2.1 hgw.2.2.2.2 hl).trans
    (residueError_mono hx hgw.2.2.1 hl)

theorem harmonic_residue_distribution_rapid {α : Type*} {l : Filter α}
    {X W K H V k : α → ℕ}
    (hD : PowerDominates l (fun w => (X w : ℝ))
      (fun w => (samplingSize (W w) (K w) (H w) (V w) : ℝ)))
    (hV : ∀ᶠ w in l, 1 ≤ V w)
    (hg : ∀ᶠ w in l, 0 < W w ∧ 0 < k w ∧ k w ≤ K w ∧ (W w).Coprime (k w)) :
    RapidlySmall l (fun w => (V w : ℝ))
      (fun w => ∑ a : Fin (k w),
        |residueProbability (X w) (W w) (k w) a.val - (k w : ℝ)⁻¹|) := by
  apply (residueError_rapid hD hV).of_abs_le
  filter_upwards [sampling_eventually_geometry hD, hg] with w hw hgw
  have hx : 2 ≤ X w := by omega
  have hl := sampling_denominator_pos hw.1 hw.2.1
  have hb := samplingSize_bounds (W w) (K w) (H w) (V w)
  have hc := residueError_polynomial (K := K w)
    (Q := (samplingSize (W w) (K w) (H w) (V w) : ℝ)) hw.1 hw.2.1
    (by exact_mod_cast hb.1) (by exact_mod_cast hb.2.1) (by exact_mod_cast hb.2.2.1)
  rw [abs_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)), abs_of_nonneg hc.1]
  exact (harmonic_residue_total_mass_error hx hgw.1 hgw.2.1 hgw.2.2.2 hl).trans
    (residueError_mono hx hgw.2.2.1 hl)

theorem harmonic_translation_rapid {α : Type*} {l : Filter α}
    {X W K H V : α → ℕ} {h : α → ℤ}
    (hD : PowerDominates l (fun w => (X w : ℝ))
      (fun w => (samplingSize (W w) (K w) (H w) (V w) : ℝ)))
    (hV : ∀ᶠ w in l, 1 ≤ V w)
    (hg : ∀ᶠ w in l, 0 < W w ∧ (W w : ℤ) ∣ h w ∧ (h w).natAbs ≤ H w) :
    RapidlySmall l (fun w => (V w : ℝ)) (fun w =>
      FiniteMass.distance ((integerMass (X w) (W w)).mapDomain (fun z => z + h w))
        (integerMass (X w) (W w))) := by
  apply (translationError_rapid hD hV).of_abs_le
  filter_upwards [sampling_eventually_geometry hD, hg] with w hw hgw
  have hx : 2 ≤ X w := by omega
  have hl := sampling_denominator_pos hw.1 hw.2.1
  have hXR : (0 : ℝ) < X w := by exact_mod_cast (by omega : 0 < X w)
  have hdpos := mul_pos hXR (sub_pos.mpr hl)
  have hb := samplingSize_bounds (W w) (K w) (H w) (V w)
  have hc := translationError_polynomial (H := H w)
    (Q := (samplingSize (W w) (K w) (H w) (V w) : ℝ)) hw.1 hw.2.1
    (by exact_mod_cast hb.1) (by exact_mod_cast hb.2.2.2.1)
  rw [abs_of_nonneg (FiniteMass.distance_nonneg _ _), translationError, abs_of_nonneg hc.1]
  have hh : |(h w : ℝ)| ≤ H w := by
    have he : ((h w).natAbs : ℝ) = |(h w : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    rw [← he]
    exact_mod_cast hgw.2.2
  exact (integer_harmonic_translation_error hx hgw.1 hl hgw.2.1).trans
    ((min_le_right _ _).trans (div_le_div_of_nonneg_right (by linarith) hdpos.le))

theorem harmonic_dilation_rapid {α : Type*} {l : Filter α}
    {X W K V k : α → ℕ}
    (hD : PowerDominates l (fun w => Real.log (X w))
      (fun w => (samplingSize (W w) (K w) 0 (V w) : ℝ)))
    (hV : ∀ᶠ w in l, 1 ≤ V w)
    (hg : ∀ᶠ w in l, 0 < W w ∧ 0 < k w ∧ k w ≤ K w ∧ (W w).Coprime (k w)) :
    RapidlySmall l (fun w => (V w : ℝ)) (fun w =>
      FiniteMass.distance ((integerMass (X w) (W w)).mapDomain (fun z => (k w : ℤ) * z))
        (integerEtaMass (X w) (W w) (k w))) := by
  have hK : ∀ᶠ w in l, 1 ≤ K w := hg.mono (fun w hw => by omega)
  apply (dilationError_rapid hD hK hV).of_abs_le
  filter_upwards [sampling_eventually_geometry (powerDominates_log_to_cutoff hD), hg, hK]
    with w hw hgw hKw
  have hx : 2 ≤ X w := by omega
  have hl := sampling_denominator_pos hw.1 hw.2.1
  have hb := samplingSize_bounds (W w) (K w) 0 (V w)
  have hc := dilationError_polynomial (Q := (samplingSize (W w) (K w) 0 (V w) : ℝ))
    hw.1 hw.2.1 hKw (by exact_mod_cast hb.1)
    (by exact_mod_cast hb.2.1) (by exact_mod_cast hb.2.2.1)
  rw [abs_of_nonneg (FiniteMass.distance_nonneg _ _), abs_of_nonneg hc.1]
  exact (integer_harmonic_dilation_error hx hgw.1 hgw.2.1
    (hgw.2.2.1.trans hw.2.2) hgw.2.2.2 hl).trans
      (dilationError_mono hx hgw.2.1 hgw.2.2.1 hl)

/-- Every fixed polynomial bound on a real-valued test function is absorbed
by the inverse-power error estimates. No probability normalization of the
comparison is assumed. -/
theorem expectation_transfer_rapid {α β : Type*} {l : Filter α}
    {V : α → ℕ} {μ ν : α → FiniteMass.Mass β} {e : α → ℝ}
    (hV : ∀ᶠ w in l, 0 < V w)
    (he : RapidlySmall l (fun w => (V w : ℝ)) e)
    (hd : ∀ᶠ w in l, FiniteMass.distance (μ w) (ν w) ≤ e w)
    (B : ℕ) (f : α → β → ℝ)
    (hf : ∀ᶠ w in l, ∀ b, |f w b| ≤ (V w : ℝ) ^ B) :
    RapidlySmall l (fun w => (V w : ℝ))
      (fun w => FiniteMass.expectation (μ w) (f w) - FiniteMass.expectation (ν w) (f w)) := by
  apply (he.mul_power (hV.mono (fun _ hw => by exact_mod_cast hw)) B).of_abs_le
  filter_upwards [hd, hf] with w hdw hfw
  exact (FiniteMass.expectation_difference_bound (μ w) (ν w) (f w) ((V w : ℝ) ^ B) hfw).trans
    ((mul_le_mul_of_nonneg_left hdw (pow_nonneg (Nat.cast_nonneg _) B)).trans (le_abs_self _))

end Hindman168
