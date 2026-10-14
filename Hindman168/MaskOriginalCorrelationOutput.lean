import Hindman168.MaskFullCorrelationOutput
import Hindman168.MaskInitialSubsetInputs

/-! The full arbitrary-target estimate on the paper's original subset
average, with a concrete detection tolerance and a zero-limit transfer
from its actual repeated target cube. No cube decay is assumed proved
for an arbitrary target. -/

set_option maxHeartbeats 2000000

namespace Hindman168
open Filter
open scoped Topology Classical

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m+1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m+1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
  (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)

def maskOriginalSubsetAdmissible (w : ℕ)
    (f : NonemptyColumnSubset (m+1) → ℤ → ℝ) (b : Finset (Fin (m+1)) → ℤ → ℝ) : Prop :=
  (∀ U y, |f U y| ≤ 1 + maskSubsetTailMask gap C w U y) ∧
  (∀ V ∈ (Finset.univ : Finset (Fin (m+1))).powerset.erase ∅, ∀ y, |b V y| ≤ 1)

noncomputable def maskSourceNonemptySupport (m : ℕ) (t : Fin (Fintype.card (LargeColumnSubset m))) :
    NonemptyColumnSubset (m+1) :=
  ⟨maskSourceSupport m t, Finset.card_pos.mp ((by decide : 0 < 2).trans_le (maskSourceSupport_card m t))⟩

theorem maskInitialSubsetInput_hasTarget (S : Finset (Fin (m+1))) (hS : 2 ≤ S.card) (w : ℕ)
    (f : NonemptyColumnSubset (m+1) → ℤ → ℝ) (b : Finset (Fin (m+1)) → ℤ → ℝ)
    (hf : maskOriginalSubsetAdmissible gap C w f b) :
    maskStageInputHasTarget S hS gap C (maskInitialSubsetInput gap C S hS w f b hf.1 hf.2)
      (f ⟨S, Finset.card_pos.mp ((by decide : 0 < 2).trans_le hS)⟩) := by
  intro x
  change f ((Fintype.equivFin (NonemptyColumnSubset (m+1))).symm
    (initialMaskRowIndex S (Finset.card_pos.mp ((by decide : 0 < 2).trans_le hS)))) = _
  simp only [initialMaskRowIndex, Equiv.symm_apply_apply]

include ha hC hJ hgap htail in
theorem maskOriginalSubset_all_supports_output_uniform :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop, ∀ t : Fin (Fintype.card (LargeColumnSubset m)),
      ∀ f : NonemptyColumnSubset (m+1) → ℤ → ℝ, ∀ b : Finset (Fin (m+1)) → ℤ → ℝ,
      maskOriginalSubsetAdmissible gap C w f b →
      |maskOriginalSubsetCorrelation gap a C w f b| ^ maskFullCorrelationPower gap t ≤
        maskFullOutputCoefficient m * |maskEndpointTargetCube gap C t J w (f (maskSourceNonemptySupport m t))| + ε := by
  intro ε hε
  filter_upwards [maskFullCorrelation_all_supports_output_uniform gap a ha C hC J hJ hgap htail ε hε] with w hw
  intro t f b hf
  have he := hw t (f (maskSourceNonemptySupport m t))
    (maskInitialSubsetInput gap C (maskSourceSupport m t) (maskSourceSupport_card m t) w f b hf.1 hf.2)
    (maskInitialSubsetInput_hasTarget gap C _ _ w f b hf)
  rw [maskInitialSubsetInput_correlation] at he
  exact he

noncomputable def maskFullDetectionTolerance (ε : ℝ) : ℝ :=
  (ε ^ maskFullCorrelationPower gap t / 2) / (maskFullOutputCoefficient m + 1)

theorem maskFullDetectionTolerance_pos {ε : ℝ} (hε : 0 < ε) :
    0 < maskFullDetectionTolerance gap t ε := by
  have hC := maskFullOutputCoefficient_ge_one m
  unfold maskFullDetectionTolerance
  positivity

include ha hC hJ hgap htail in
theorem maskOriginalSubset_detection_uniform {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w in atTop, ∀ f : NonemptyColumnSubset (m+1) → ℤ → ℝ, ∀ b : Finset (Fin (m+1)) → ℤ → ℝ,
      maskOriginalSubsetAdmissible gap C w f b →
      |maskEndpointTargetCube gap C t J w (f (maskSourceNonemptySupport m t))| ≤
        maskFullDetectionTolerance gap t ε → |maskOriginalSubsetCorrelation gap a C w f b| ≤ ε := by
  have hp := maskFullCorrelationPower_pos gap t
  have hz : 0 < ε ^ maskFullCorrelationPower gap t := pow_pos hε _
  have hδ := maskFullDetectionTolerance_pos gap t hε
  have hK := maskFullOutputCoefficient_ge_one m
  have hn : maskFullOutputCoefficient m + 1 ≠ 0 := by linarith
  have heq : (maskFullOutputCoefficient m + 1) * maskFullDetectionTolerance gap t ε =
      ε ^ maskFullCorrelationPower gap t / 2 := by
    unfold maskFullDetectionTolerance
    field_simp
  have hprod : maskFullOutputCoefficient m * maskFullDetectionTolerance gap t ε ≤
      ε ^ maskFullCorrelationPower gap t / 2 := by nlinarith
  filter_upwards [maskOriginalSubset_all_supports_output_uniform gap a ha C hC J hJ hgap htail
    (ε ^ maskFullCorrelationPower gap t / 2) (by positivity)] with w hw
  intro f b hf hcube
  have h := (hw t f b hf).trans
    (add_le_add (mul_le_mul_of_nonneg_left hcube (by linarith)) le_rfl)
  have hb : |maskOriginalSubsetCorrelation gap a C w f b| ^ maskFullCorrelationPower gap t ≤
      ε ^ maskFullCorrelationPower gap t := by linarith
  by_contra! hbad
  have hs := pow_lt_pow_left₀ hbad hε.le (Nat.ne_of_gt hp)
  exact (not_lt_of_ge hb) hs

include ha hC hJ hgap htail in
theorem maskOriginalSubset_tendsto_zero_of_targetCube
    (f : ℕ → NonemptyColumnSubset (m+1) → ℤ → ℝ) (b : ℕ → Finset (Fin (m+1)) → ℤ → ℝ)
    (hf : ∀ᶠ w in atTop, maskOriginalSubsetAdmissible gap C w (f w) (b w))
    (hcube : Tendsto (fun w => maskEndpointTargetCube gap C t J w (f w (maskSourceNonemptySupport m t)))
      atTop (𝓝 0)) :
    Tendsto (fun w => maskOriginalSubsetCorrelation gap a C w (f w) (b w)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply tendsto_order.2
  constructor
  · intro c hc
    exact Eventually.of_forall (fun _ => hc.trans_le (abs_nonneg _))
  · intro ε hε
    have hδ := maskFullDetectionTolerance_pos gap t (by linarith : 0 < ε/2)
    filter_upwards [maskOriginalSubset_detection_uniform gap a ha C hC t J hJ hgap htail
      (by linarith : 0 < ε/2), hf,
      hcube.abs.eventually (eventually_lt_nhds (by simpa only [abs_zero] using hδ))] with w hw hfw hcw
    exact (hw (f w) (b w) hfw hcw.le).trans_lt (by linarith)

end Hindman168
