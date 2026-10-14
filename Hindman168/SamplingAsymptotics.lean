import Hindman168.PowerGrowth
import Hindman168.SamplingMajorants

/-!
# The harmonic sampling errors at every inverse-power scale

The hypotheses are the paper's growth conditions on X or log X, rather
than small-error premises. Rates use the cutoff K or H, independently of
which admissible residue, dilation or translation parameter is chosen.
-/

namespace Hindman168

open Filter Asymptotics
open scoped Topology BigOperators

def samplingSize (W K H V : ℕ) : ℕ := 2 + W + K + H + V

theorem samplingSize_bounds (W K H V : ℕ) :
    2 ≤ samplingSize W K H V ∧ W ≤ samplingSize W K H V ∧
    K ≤ samplingSize W K H V ∧ H ≤ samplingSize W K H V ∧
    V ≤ samplingSize W K H V := by
  unfold samplingSize
  omega

theorem nat_log_nonneg (X : ℕ) : 0 ≤ Real.log (X : ℝ) := by
  by_cases hX : X = 0
  · simp [hX]
  · exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ X))

theorem powerDominates_log_to_cutoff {α : Type*} {l : Filter α} {X : α → ℕ} {Q : α → ℝ}
    (hD : PowerDominates l (fun w => Real.log (X w)) Q) :
    PowerDominates l (fun w => (X w : ℝ)) Q :=
  hD.mono_right (Eventually.of_forall (fun w =>
    ⟨nat_log_nonneg (X w), Real.log_le_self (Nat.cast_nonneg (X w))⟩))

/-- Growth also supplies the hypotheses needed in the finite estimates. -/
theorem sampling_eventually_geometry {α : Type*} {l : Filter α}
    {X W K H V : α → ℕ}
    (hD : PowerDominates l (fun w => (X w : ℝ))
      (fun w => (samplingSize (W w) (K w) (H w) (V w) : ℝ))) :
    ∀ᶠ w in l, 4 ≤ X w ∧ 2 * W w ≤ X w ∧ K w ≤ X w := by
  filter_upwards [hD.eventually_bound (Eventually.of_forall (fun w => Nat.cast_nonneg (X w)))
    (Eventually.of_forall (fun w => Nat.cast_nonneg (samplingSize (W w) (K w) (H w) (V w))))
    1 (by norm_num : (0 : ℝ) < 4)] with w hw
  simp only [pow_one] at hw
  have hb := samplingSize_bounds (W w) (K w) (H w) (V w)
  have hQ : (2 : ℝ) ≤ samplingSize (W w) (K w) (H w) (V w) := by exact_mod_cast hb.1
  have hWQ : (W w : ℝ) ≤ samplingSize (W w) (K w) (H w) (V w) := by exact_mod_cast hb.2.1
  have hKQ : (K w : ℝ) ≤ samplingSize (W w) (K w) (H w) (V w) := by exact_mod_cast hb.2.2.1
  refine ⟨?_, ?_, ?_⟩
  · have hx : (4 : ℝ) ≤ X w := by linarith
    exact_mod_cast hx
  · have hx : (2 : ℝ) * W w ≤ X w := by nlinarith
    exact_mod_cast hx
  · have hx : (K w : ℝ) ≤ X w := by linarith
    exact_mod_cast hx

theorem sampling_eventually_valid {α : Type*} {l : Filter α}
    {X W K H V : α → ℕ}
    (hD : PowerDominates l (fun w => (X w : ℝ))
      (fun w => (samplingSize (W w) (K w) (H w) (V w) : ℝ)))
    (hW : ∀ᶠ w in l, 0 < W w) :
    ∀ᶠ w in l, 2 ≤ X w ∧ (W w : ℝ) / X w < Real.log (X w) ∧
      0 < harmonicNormalizer (X w) (W w) := by
  filter_upwards [sampling_eventually_geometry hD, hW] with w hw hWw
  have hx : 2 ≤ X w := by omega
  have hl := sampling_denominator_pos hw.1 hw.2.1
  exact ⟨hx, hl, harmonicNormalizer_pos hx hWw hl⟩

theorem residueError_rapid {α : Type*} {l : Filter α} {X W K H V : α → ℕ}
    (hD : PowerDominates l (fun w => (X w : ℝ))
      (fun w => (samplingSize (W w) (K w) (H w) (V w) : ℝ)))
    (hV : ∀ᶠ w in l, 1 ≤ V w) :
    RapidlySmall l (fun w => (V w : ℝ)) (fun w => residueError (X w) (W w) (K w)) := by
  have hg := sampling_eventually_geometry hD
  apply rapid_of_polynomial_majorant hD
    (hg.mono (fun w hw => by exact_mod_cast (by omega : 0 < X w)))
    (hV.mono (fun w hw => ⟨by exact_mod_cast hw,
      by exact_mod_cast (samplingSize_bounds (W w) (K w) (H w) (V w)).2.2.2.2⟩))
    2 (by norm_num : (0 : ℝ) < 4)
  filter_upwards [hg] with w hw
  have hb := samplingSize_bounds (W w) (K w) (H w) (V w)
  have he := residueError_polynomial (K := K w)
    (Q := (samplingSize (W w) (K w) (H w) (V w) : ℝ)) hw.1 hw.2.1
    (by exact_mod_cast hb.1) (by exact_mod_cast hb.2.1) (by exact_mod_cast hb.2.2.1)
  simpa only [abs_of_nonneg he.1] using he.2

noncomputable def translationError (X W H : ℕ) : ℝ :=
  2 * (H : ℝ) / (X * (Real.log X - (W : ℝ) / X))

theorem translationError_rapid {α : Type*} {l : Filter α} {X W K H V : α → ℕ}
    (hD : PowerDominates l (fun w => (X w : ℝ))
      (fun w => (samplingSize (W w) (K w) (H w) (V w) : ℝ)))
    (hV : ∀ᶠ w in l, 1 ≤ V w) :
    RapidlySmall l (fun w => (V w : ℝ)) (fun w => translationError (X w) (W w) (H w)) := by
  have hg := sampling_eventually_geometry hD
  apply rapid_of_polynomial_majorant hD
    (hg.mono (fun w hw => by exact_mod_cast (by omega : 0 < X w)))
    (hV.mono (fun w hw => ⟨by exact_mod_cast hw,
      by exact_mod_cast (samplingSize_bounds (W w) (K w) (H w) (V w)).2.2.2.2⟩))
    1 (by norm_num : (0 : ℝ) < 4)
  filter_upwards [hg] with w hw
  have hb := samplingSize_bounds (W w) (K w) (H w) (V w)
  have he := translationError_polynomial (H := H w)
    (Q := (samplingSize (W w) (K w) (H w) (V w) : ℝ)) hw.1 hw.2.1
    (by exact_mod_cast hb.1) (by exact_mod_cast hb.2.2.2.1)
  change |translationError (X w) (W w) (H w)| ≤ _
  simpa only [translationError, pow_one, abs_of_nonneg he.1] using he.2

theorem dilationError_rapid {α : Type*} {l : Filter α} {X W K V : α → ℕ}
    (hD : PowerDominates l (fun w => Real.log (X w))
      (fun w => (samplingSize (W w) (K w) 0 (V w) : ℝ)))
    (hK : ∀ᶠ w in l, 1 ≤ K w) (hV : ∀ᶠ w in l, 1 ≤ V w) :
    RapidlySmall l (fun w => (V w : ℝ)) (fun w => dilationError (X w) (W w) (K w)) := by
  have hg := sampling_eventually_geometry (powerDominates_log_to_cutoff hD)
  apply rapid_of_polynomial_majorant hD
    (hg.mono (fun w hw => by have hl := sampling_log_lower hw.1; linarith))
    (hV.mono (fun w hw => ⟨by exact_mod_cast hw,
      by exact_mod_cast (samplingSize_bounds (W w) (K w) 0 (V w)).2.2.2.2⟩))
    2 (by norm_num : (0 : ℝ) < 8)
  filter_upwards [hg, hK] with w hw hKw
  have hb := samplingSize_bounds (W w) (K w) 0 (V w)
  have he := dilationError_polynomial
    (Q := (samplingSize (W w) (K w) 0 (V w) : ℝ)) hw.1 hw.2.1 hKw
    (by exact_mod_cast hb.1) (by exact_mod_cast hb.2.1) (by exact_mod_cast hb.2.2.1)
  simpa only [abs_of_nonneg he.1] using he.2

end Hindman168
