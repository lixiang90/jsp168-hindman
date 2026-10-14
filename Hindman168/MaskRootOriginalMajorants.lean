import Hindman168.MaskRootOriginalSampling

/-! Every subset of the complete actual enlarged row enumeration has its
power-of-two majorant mean. Injectivity is furnished by the bijection and
tail budgets by the original tail-before-gap order. -/

set_option maxHeartbeats 2000000

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

namespace MaskRootCopiedSampling

variable {m N : ℕ}

abbrev BaseRow (S : MaskRootCopiedSampling m N) := MaskOriginalBaseRow m S.gap S.template

noncomputable def rows (S : MaskRootCopiedSampling m N)
    (_ : ℕ) (u : Fin (Fintype.card (MaskRootCopiedRow m S.gap S.template))) :
    MaskRootCopiedRow m S.gap S.template := (Fintype.equivFin _).symm u

noncomputable def labels (S : MaskRootCopiedSampling m N)
    (label : ℕ → S.BaseRow → Fin (m + 1)) (w : ℕ)
    (u : Fin (Fintype.card (MaskRootCopiedRow m S.gap S.template))) : Fin (m + 1) :=
  label w (S.rows w u).val.1.val.1

theorem rows_injective (S : MaskRootCopiedSampling m N) (w : ℕ) :
    Function.Injective (S.rows w) := (Fintype.equivFin _).symm.injective

noncomputable def fullMajorant (S : MaskRootCopiedSampling m N)
    (label : ℕ → S.BaseRow → Fin (m + 1))
    (U : Finset (Fin (Fintype.card (MaskRootCopiedRow m S.gap S.template)))) : ℕ → ℝ :=
  S.normalizedMajorant (S.labels label) S.rows U

theorem fullMajorant_tendsto (S : MaskRootCopiedSampling m N)
    (label : ℕ → S.BaseRow → Fin (m + 1))
    (hdivbudget : ∀ᶠ w in atTop, ∀ base,
      tailBound ((S.chain w).tailCutoffs ((maskGeneratedMaster m S.gap).cutoff w) (label w base)) ≤ S.budget w)
    (U : Finset (Fin (Fintype.card (MaskRootCopiedRow m S.gap S.template)))) :
    Tendsto (S.fullMajorant label U) atTop (𝓝 (((2 ^ U.card : ℕ) : ℝ))) :=
  S.normalizedMajorant_tendsto (S.labels label) S.rows
    (Eventually.of_forall S.rows_injective)
    (hdivbudget.mono (fun w hw u => hw (S.rows w u).val.1.val.1)) U

end MaskRootCopiedSampling

namespace MaskRootOriginalSampling

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)

local notation "S" => maskRootOriginalSampling m gap a ha C hC t J hJ hgap

theorem divisor_budget
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val) :
    ∀ᶠ w in atTop, ∀ col,
      tailBound (((S).chain w).tailCutoffs ((maskGeneratedMaster m (S).gap).cutoff w) col) ≤ (S).budget w := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  filter_upwards [htail] with w hw
  intro col
  exact hF.chain_tail_budget_at_gap (C w) w col (gap w).val (hw col)

theorem fullMajorant_tendsto
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → (S).BaseRow → Fin (m + 1))
    (U : Finset (Fin (Fintype.card (MaskRootCopiedRow m (S).gap (S).template)))) :
    Tendsto ((S).fullMajorant label U) atTop (𝓝 (((2 ^ U.card : ℕ) : ℝ))) :=
  (S).fullMajorant_tendsto label
    ((divisor_budget gap a ha C hC t J hJ hgap htail).mono (fun _ hw _ => hw _)) U

end MaskRootOriginalSampling
end Hindman168
