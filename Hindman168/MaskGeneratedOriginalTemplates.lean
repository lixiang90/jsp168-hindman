import Hindman168.TargetedMaskRowIteration
import Hindman168.OriginalRowTemplateFamily

/-!
# Instantiating the original template/master/model pipeline with mask rows

All tracked supports of size at least two are enumerated. Their actual
finite mask iterations supply row anchors and pair minors with no such
hypotheses in this application. Each has exactly 2q local prime slots,
embedded in one fixed master arity. The generated catalogues and the extra
zero-prime type then supply one model sequence at every fixed positive scale.
Only the analytic block/gap/rho and companion-stage data remain explicit.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

abbrev LargeColumnSubset (m : ℕ) := {S : Finset (Fin (m + 1)) // 2 ≤ S.card}

noncomputable instance (m : ℕ) : Fintype (LargeColumnSubset m) := Fintype.ofFinite _

def maskRowCountBound (m : ℕ) : ℕ :=
  (2 ^ (m + 1) - 1) * 2 ^ (2 ^ (m + 1) - 1)

def maskMasterArity (m : ℕ) : ℕ := 2 * (2 ^ (m + 1) - 1)

noncomputable def maskGeneratedRowData {m N : ℕ}
    (S : Finset (Fin (m + 1))) (hS : 2 ≤ S.card) (gap : ℕ → Fin N) :
    OriginalPolynomialRowData (maskMasterArity m) N where
  arity := (fullMaskRowStage S hS).primeArity
  rowCount := (fullMaskRowStage S hS).rowCount
  offColumns := m
  rows := (fullMaskRowStage S hS).rows
  rowCount_gt_one := by have h := fullMaskRowStage_rowCount_ge S hS; omega
  target := (fullMaskRowStage S hS).target
  slot := Fin.cast (fullMaskRowStage_primeArity S hS)
  slot_injective := (finCongr (fullMaskRowStage_primeArity S hS)).injective
  gap := gap

theorem maskGeneratedRowData_dimension_le {m N : ℕ}
    (S : Finset (Fin (m + 1))) (hS : 2 ≤ S.card) (gap : ℕ → Fin N) :
    (maskGeneratedRowData S hS gap).rowCount - 1 ≤ maskRowCountBound m := by
  exact (Nat.sub_le _ _).trans (fullMaskRowStage_rowCount_le S hS)

noncomputable def maskGeneratedRowDataFamily (m : ℕ) {N : ℕ} (gap : ℕ → Fin N) :
    Fin (Fintype.card (LargeColumnSubset m)) → OriginalPolynomialRowData (maskMasterArity m) N :=
  fun t => maskGeneratedRowData ((Fintype.equivFin (LargeColumnSubset m)).symm t).val
    ((Fintype.equivFin (LargeColumnSubset m)).symm t).property gap

theorem maskGeneratedRowDataFamily_dimension_le (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) :
    (maskGeneratedRowDataFamily m gap t).rowCount - 1 ≤ maskRowCountBound m :=
  maskGeneratedRowData_dimension_le _ _ gap

noncomputable def maskGeneratedMaster (m : ℕ) {N : ℕ} (gap : ℕ → Fin N) : MasterParameterFamily :=
  originalRowMaster (maskGeneratedRowDataFamily m gap)

theorem maskGeneratedMaster_conditions (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (A : Finset ℚ) (hA : ∀ a ∈ A, 0 < a) :
    MasterParameterConditions N A (originalRowMasterCatalog (maskGeneratedRowDataFamily m gap))
      (maskGeneratedMaster m gap) :=
  originalRowMaster_conditions _ A hA

noncomputable def maskGeneratedDualTemplates (m : ℕ) {N : ℕ}
    (gap : ℕ → Fin N) (d₀ : ℕ) (gap₀ : ℕ → Fin N) :
    Fin (Fintype.card (LargeColumnSubset m) + 1) → OriginalDualTemplate (maskMasterArity m) N 1 :=
  originalRowAndZeroTemplates (maskGeneratedRowDataFamily m gap) d₀ gap₀

theorem maskGenerated_all_positive_scales_models (m : ℕ) {N b : ℕ}
    (gap : ℕ → Fin N) (A : Finset ℚ) (hA : ∀ a ∈ A, 0 < a)
    (d₀ d : ℕ) (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ d) (hd : maskRowCountBound m ≤ d)
    (gap₀ : ℕ → Fin N) (C : ℕ → Chain b)
    (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → Fin b) (tail : ℕ → Finset ℕ)
    (htail : ∀ᶠ w in atTop, (C w).tail (label w) ⊆ tail w)
    (root : ℕ → Fin N) (htailroot : ∀ᶠ w in atTop, tail w ⊆ Finset.range (root w).val)
    (htailgap : ∀ᶠ w in atTop, tail w ⊆ Finset.range (gap w).val)
    (hgap : ∀ᶠ w in atTop, (gap w).val ≤ (root w).val)
    (htail₀ : ∀ᶠ w in atTop, tail w ⊆ Finset.range (gap₀ w).val)
    (hgap₀ : ∀ᶠ w in atTop, (gap₀ w).val ≤ (root w).val)
    (ρ : ℕ → ℤ → ℝ)
    (hρ : ∀ᶠ w in atTop, ∀ y, 0 ≤ ρ w y ∧ ρ w y ≤ masterPredictionBlockMask (maskGeneratedMaster m gap) C label w y)
    (P : ℕ → ℕ → Prop) (hP : ∀ q, ∀ᶠ w in atTop, P q w) :
    ∃ (stage : ℕ → ℕ) (model : ℕ → ℤ → ℝ), Tendsto stage atTop atTop ∧
      (∀ w, stage w ≤ w) ∧ (∀ w y, 0 ≤ model w y ∧ model w y ≤ 1) ∧
      (∀ᶠ w in atTop, P (stage w) w) ∧
      ∀ t : Fin (Fintype.card (LargeColumnSubset m) + 1), ∀ j : ℕ, 1 ≤ j →
        ∀ η : ℝ, 0 < η → ∀ᶠ w in atTop,
        ∀ u : OriginalSingleDualInput (maskGeneratedDualTemplates m gap d₀ gap₀ t).arity
          (maskGeneratedDualTemplates m gap d₀ gap₀ t).dimension,
          u.Admissible (maskGeneratedMaster m gap) C label w →
          |expectation (integerMass ((maskGeneratedMaster m gap).cutoff w (root w).val) (primorial w))
            (fun y => (ρ w y - model w y) *
              (maskGeneratedDualTemplates m gap d₀ gap₀ t).dual (maskGeneratedMaster m gap) (fun _ => j) u w y)| < η := by
  exact originalRowAndZero_all_positive_scales_models (maskGeneratedRowDataFamily m gap) A hA
    d₀ d hd₀ hd₀max (fun t => (maskGeneratedRowDataFamily_dimension_le m gap t).trans hd)
    gap₀ C hN label tail htail root htailroot htail₀ hgap₀ (fun _ => htailgap) (fun _ => hgap)
    ρ hρ P hP

end Hindman168
