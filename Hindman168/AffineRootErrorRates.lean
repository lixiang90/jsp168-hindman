import Hindman168.HarmonicAffineRoot

/-! A fixed polynomial cap for all admissible affine parameters, and its
rapid decay derived from logarithmic cutoff growth. The cap need not
have the sharp finite boundary constant used in the paper. -/

namespace Hindman168

open Filter Asymptotics
open scoped Topology Classical

noncomputable def affineRootErrorCap (X W K H V : ℕ) : ℝ :=
  12 * (samplingSize W K H V : ℝ) ^ 2 / Real.log X

theorem affineRootError_polynomial {X W k H : ℕ} {Q : ℝ}
    (hX : 4 ≤ X) (hWX : 2 * W ≤ X) (hk : 1 ≤ k) (hQ : 2 ≤ Q)
    (hWQ : (W : ℝ) ≤ Q) (hkQ : (k : ℝ) ≤ Q) (hHQ : (H : ℝ) ≤ Q) :
    0 ≤ affineRootError X W k H ∧ affineRootError X W k H ≤ 12 * Q ^ 2 / Real.log X := by
  have hd := dilationError_polynomial hX hWX hk hQ hWQ hkQ
  have ht := translationError_polynomial hX hWX hQ hHQ
  have hl : 0 < Real.log (X : ℝ) := lt_of_lt_of_le (by norm_num) (sampling_log_lower hX)
  have hx : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hmul : (k : ℝ) * translationError X W H ≤ 4 * Q ^ 2 / X := by
    have he := mul_le_mul hkQ ht.2 (by simpa only [translationError] using ht.1) (by linarith : 0 ≤ Q)
    calc
      _ ≤ Q * (4 * Q / X) := he
      _ = _ := by ring
  have hb : 4 * Q ^ 2 / X ≤ 4 * Q ^ 2 / Real.log X :=
    div_le_div_of_nonneg_left (by positivity) hl (Real.log_le_self (Nat.cast_nonneg X))
  unfold affineRootError
  constructor
  · exact add_nonneg hd.1 (mul_nonneg (Nat.cast_nonneg k) (by simpa only [translationError] using ht.1))
  · calc
      _ ≤ 8 * Q ^ 2 / Real.log X + 4 * Q ^ 2 / Real.log X :=
        add_le_add hd.2 (hmul.trans hb)
      _ = _ := by ring

theorem affineRootError_le_cap {X W K H V k : ℕ} {h : ℤ}
    (hX : 4 ≤ X) (hWX : 2 * W ≤ X) (hk : 0 < k) (hkK : k ≤ K) (hhH : h.natAbs ≤ H) :
    affineRootError X W k h.natAbs ≤ affineRootErrorCap X W K H V := by
  have hs := samplingSize_bounds W K H V
  exact (affineRootError_polynomial hX hWX (by omega) (by exact_mod_cast hs.1)
    (by exact_mod_cast hs.2.1) (by exact_mod_cast hkK.trans hs.2.2.1)
    (by exact_mod_cast hhH.trans hs.2.2.2.1)).2

theorem affineRootErrorCap_rapid {α : Type*} {l : Filter α} {X W K H V : α → ℕ}
    (hD : PowerDominates l (fun w => Real.log (X w))
      (fun w => (samplingSize (W w) (K w) (H w) (V w) : ℝ)))
    (hV : ∀ᶠ w in l, 1 ≤ V w) :
    RapidlySmall l (fun w => (V w : ℝ))
      (fun w => affineRootErrorCap (X w) (W w) (K w) (H w) (V w)) := by
  have hg := sampling_eventually_geometry (powerDominates_log_to_cutoff hD)
  apply rapid_of_polynomial_majorant hD
    (hg.mono (fun w hw => lt_of_lt_of_le (by norm_num) (sampling_log_lower hw.1)))
    (hV.mono (fun w hw => ⟨by exact_mod_cast hw,
      by exact_mod_cast (samplingSize_bounds (W w) (K w) (H w) (V w)).2.2.2.2⟩))
    2 (by norm_num : (0 : ℝ) < 12)
  filter_upwards [hg] with w hw
  have hl : 0 < Real.log (X w : ℝ) :=
    lt_of_lt_of_le (by norm_num) (sampling_log_lower hw.1)
  unfold affineRootErrorCap
  rw [abs_of_nonneg (by positivity)]

end Hindman168
