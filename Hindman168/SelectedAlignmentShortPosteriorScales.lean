import Hindman168.SelectedAlignmentShortPosteriorLaw

namespace Hindman168
open Filter
open scoped BigOperators Topology Classical

theorem selected_alignment_shortPosterior_scales_eventually
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (i gap : Fin n) (hgap : gap ≤ i) (T : Finset (Fin n)) :
    ∀ᶠ w in atTop,
      0 < alignedSqrtMicrocellWidth (F.gap w gap.val) (F.modulus w) ∧
      alignedSqrtMicrocellWidth (F.gap w gap.val) (F.modulus w) ≤ F.cutoff w i.val ∧
      2 * (2 ^ T.card : ℝ) * (F.modulus w : ℕ) /
        alignedSqrtMicrocellWidth (F.gap w gap.val) (F.modulus w) ≤ 1 / 2 := by
  have hratio := hF.cell_width_cutoff_ratio_tendsto (fun _ => gap) (fun _ => i)
    (Eventually.of_forall (fun _ => hgap))
  filter_upwards [master_microcell_eventually_positive hF (fun _ => gap),
    hratio.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    master_microcell_eventually_polynomial_small hF (fun _ => gap) 1 (2 * 2 ^ T.card)
      (by norm_num : (0 : ℝ) < 1 / 2)] with w hR hr hs
  have hx : (0 : ℝ) < F.cutoff w i.val := by exact_mod_cast hF.cutoff_positive w i.val
  have hgap : F.gap w gap.val ≤ F.cutoff w i.val := by
    have hh := (div_lt_iff₀ hx).mp hr
    simp only [one_mul] at hh
    exact_mod_cast hh.le
  refine ⟨hR, (alignedSqrtWidth_le _ _).trans hgap, ?_⟩
  have hR' : (0 : ℝ) < alignedSqrtMicrocellWidth (F.gap w gap.val) (F.modulus w) := by exact_mod_cast hR
  apply (div_le_iff₀ hR').mpr
  apply le_trans _ hs
  simp only [pow_one]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast F.modulus_le_auxiliary w gap.val) (by positivity)

end Hindman168
