import Hindman168.MaskInitialSubsetInputs

/-! Uniform decay of the paper's original subset-sum/subset-product
correlation when its distinguished factor is the actual tail mask minus
one. Other subset functions and product masks remain arbitrary within
the stated original bounds. This does not assert the arbitrary-target
model-error correlation principle or the full monochromatic theorem. -/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m+1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m+1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (J : ℕ) (hJ : 0 < J)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
  (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)

def maskOriginalSubsetCenteredAdmissible (S : Finset (Fin (m+1))) (hS : 2 ≤ S.card)
    (w : ℕ) (f : NonemptyColumnSubset (m+1) → ℤ → ℝ) (b : Finset (Fin (m+1)) → ℤ → ℝ) : Prop :=
  (∀ U y, |f U y| ≤ 1 + maskSubsetTailMask gap C w U y) ∧
  (∀ V ∈ (Finset.univ : Finset (Fin (m+1))).powerset.erase ∅, ∀ y, |b V y| ≤ 1) ∧
  f ⟨S, Finset.card_pos.mp ((by decide : 0 < 2).trans_le hS)⟩ =
    fun y => maskSubsetTailMask gap C w ⟨S, Finset.card_pos.mp ((by decide : 0 < 2).trans_le hS)⟩ y - 1

include ha hC hJ hgap htail in
theorem maskOriginalSubsetCentered_all_supports_uniform_zero :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop, ∀ S : Finset (Fin (m+1)), ∀ hS : 2 ≤ S.card,
      ∀ f : NonemptyColumnSubset (m+1) → ℤ → ℝ, ∀ b : Finset (Fin (m+1)) → ℤ → ℝ,
      maskOriginalSubsetCenteredAdmissible gap C S hS w f b →
      |maskOriginalSubsetCorrelation gap a C w f b| ≤ ε := by
  intro ε hε
  filter_upwards [maskInitialCentered_all_supports_uniform_zero gap a ha C hC J hJ hgap htail ε hε] with w hw
  intro S hS f b hf
  let P (T : LargeColumnSubset m) : Prop :=
    ∀ D : MaskStageCorrelationInput T.val T.property gap C 0 w (maskRemainingMasks m 0),
      maskStageInputHasTarget T.val T.property gap C D (maskInitialCenteredTarget gap C T.val T.property w) →
      |maskStageInputCorrelation T.val T.property gap a C D| ≤ ε
  have he : P ((Fintype.equivFin (LargeColumnSubset m)).symm
      ((Fintype.equivFin (LargeColumnSubset m)) ⟨S, hS⟩)) :=
    hw ((Fintype.equivFin (LargeColumnSubset m)) ⟨S, hS⟩)
  rw [(Fintype.equivFin (LargeColumnSubset m)).symm_apply_apply ⟨S, hS⟩] at he
  have hd := maskInitialSubsetInput_target gap C S hS w f b hf.1 hf.2.1 hf.2.2
  have hz := he (maskInitialSubsetInput gap C S hS w f b hf.1 hf.2.1) hd
  rw [maskInitialSubsetInput_correlation] at hz
  exact hz

include ha hC hJ hgap htail in
theorem maskOriginalSubsetCentered_uniform_zero (S : Finset (Fin (m+1))) (hS : 2 ≤ S.card) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop,
      ∀ f : NonemptyColumnSubset (m+1) → ℤ → ℝ, ∀ b : Finset (Fin (m+1)) → ℤ → ℝ,
      maskOriginalSubsetCenteredAdmissible gap C S hS w f b →
      |maskOriginalSubsetCorrelation gap a C w f b| ≤ ε := by
  intro ε hε
  exact (maskOriginalSubsetCentered_all_supports_uniform_zero gap a ha C hC J hJ hgap htail ε hε).mono
    (fun _ hw => hw S hS)

include ha hC hJ hgap htail in
theorem maskOriginalSubsetCentered_tendsto_zero (S : Finset (Fin (m+1))) (hS : 2 ≤ S.card)
    (f : ℕ → NonemptyColumnSubset (m+1) → ℤ → ℝ) (b : ℕ → Finset (Fin (m+1)) → ℤ → ℝ)
    (hf : ∀ᶠ w in atTop, maskOriginalSubsetCenteredAdmissible gap C S hS w (f w) (b w)) :
    Tendsto (fun w => maskOriginalSubsetCorrelation gap a C w (f w) (b w)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply tendsto_order.2
  constructor
  · intro c hc
    exact Eventually.of_forall (fun _ => hc.trans_le (abs_nonneg _))
  · intro ε hε
    filter_upwards [maskOriginalSubsetCentered_uniform_zero gap a ha C hC J hJ hgap htail S hS
      (ε / 2) (by linarith), hf] with w hw hfw
    exact (hw (f w) (b w) hfw).trans_lt (by linarith)

end Hindman168
