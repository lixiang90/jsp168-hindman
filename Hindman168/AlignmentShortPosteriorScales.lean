import Hindman168.AlignmentShortCutoffGeometry

namespace Hindman168
open Filter
open scoped BigOperators Topology Classical

theorem alignmentShortCutoffGood_volume_le {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (T : Finset (Fin n)) (x : Fin n → ℕ)
    (hX : 0 < F.cutoff w i.val)
    (hRX : alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) ≤ F.cutoff w i.val)
    (hg : alignmentShortCutoffGood F w i T x) :
    0 < alignmentShortBinStart F w i T x ∧
      alignmentShortBinVolume F w i T x ≤ alignmentShortBinStart F w i T x := by
  have ha : 0 < ∏ j ∈ T, (2 : ℕ) ^ Nat.log2 (x j) := by positivity
  have hc : 0 < (2 : ℕ) ^ T.card := by positivity
  constructor
  · exact (Nat.mul_pos hX (Nat.mul_pos hc ha)).trans_le hg.1
  · apply le_trans _ hg.1
    unfold alignmentShortBinVolume
    calc
      _ ≤ (∏ j ∈ T, 2 ^ Nat.log2 (x j)) * F.cutoff w i.val := Nat.mul_le_mul_left _ hRX
      _ = F.cutoff w i.val * (∏ j ∈ T, 2 ^ Nat.log2 (x j)) := mul_comm _ _
      _ ≤ _ := Nat.mul_le_mul_left _ (by
        calc
          (∏ j ∈ T, 2 ^ Nat.log2 (x j)) = 1 * (∏ j ∈ T, 2 ^ Nat.log2 (x j)) := (one_mul _).symm
          _ ≤ _ := Nat.mul_le_mul_right _ hc)

theorem alignment_shortPosterior_scales_eventually
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (i : Fin n) (T : Finset (Fin n)) :
    ∀ᶠ w in atTop,
      0 < alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) ∧
      alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) ≤ F.cutoff w i.val ∧
      2 * (2 ^ T.card : ℝ) * (F.modulus w : ℕ) /
        alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) ≤ 1 / 2 := by
  have hratio := hF.cell_width_cutoff_ratio_tendsto (fun _ => i) (fun _ => i)
    (Eventually.of_forall (fun _ => le_rfl))
  filter_upwards [master_microcell_eventually_positive hF (fun _ => i),
    hratio.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    master_microcell_eventually_polynomial_small hF (fun _ => i) 1 (2 * 2 ^ T.card)
      (by norm_num : (0 : ℝ) < 1 / 2)] with w hR hr hs
  have hx : (0 : ℝ) < F.cutoff w i.val := by exact_mod_cast hF.cutoff_positive w i.val
  have hgap : F.gap w i.val ≤ F.cutoff w i.val := by
    have hh := (div_lt_iff₀ hx).mp hr
    simp only [one_mul] at hh
    exact_mod_cast hh.le
  refine ⟨hR, (alignedSqrtWidth_le _ _).trans hgap, ?_⟩
  have hR' : (0 : ℝ) < alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) := by exact_mod_cast hR
  apply (div_le_iff₀ hR').mpr
  apply le_trans _ hs
  simp only [pow_one]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast F.modulus_le_auxiliary w i.val) (by positivity)

end Hindman168
