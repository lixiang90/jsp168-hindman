import Hindman168.MaskOriginalNormalizedLaw
import Hindman168.AdditiveRowInitialLaw

/-! One actual additive-row family on the whole normalized outside space.
On original good tuples it is the generated integer row-direction data;
elsewhere zero rows provide a total harmless definition. Functions and
majorants are completed off that event without changing retained integrals. -/

set_option maxHeartbeats 2000000

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

abbrev MaskOriginalBaseRow (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) :=
  ReplicaCubeRow (Fintype.card (PolynomialRowFamily.OffTargetRow
    (maskGeneratedRowDataFamily m gap t).target)) 1

abbrev MaskOriginalDirection (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) :=
  Fin (Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target))

abbrev MaskOriginalPoint (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) :=
  (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) × (Fin (m + 1) → ℤ)

namespace MaskOriginalSampling

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m)))

noncomputable def additiveData (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) :
    AdditiveRowData (Fintype.card (PolynomialRowFamily.OffTargetRow
      (maskGeneratedRowDataFamily m gap t).target)) (m + 1) :=
  if h : Nonempty ((maskGeneratedRowDataFamily m gap t).rows.AdditiveEliminationConditions
      (maskGeneratedMaster m gap) w (masterColumnCoefficient N a (fun w => (C w).block) w) x
      (maskGeneratedRowDataFamily m gap t).target) then
    (Classical.choice h).data
  else { coefficient := fun _ _ => 0, direction := fun _ _ => 0, annihilate := by intro i; simp }

theorem additiveData_certificate (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ)
    (h : Nonempty ((maskGeneratedRowDataFamily m gap t).rows.AdditiveEliminationConditions
      (maskGeneratedMaster m gap) w (masterColumnCoefficient N a (fun w => (C w).block) w) x
      (maskGeneratedRowDataFamily m gap t).target)) :
    ∃ H : (maskGeneratedRowDataFamily m gap t).rows.AdditiveEliminationConditions
      (maskGeneratedMaster m gap) w (masterColumnCoefficient N a (fun w => (C w).block) w) x
      (maskGeneratedRowDataFamily m gap t).target,
      additiveData gap a C t w x = H.data := by
  refine ⟨Classical.choice h, ?_⟩
  unfold additiveData
  rw [dif_pos h]

include ha hC in
theorem additiveData_eventually_certificate :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      ∃ H : (maskGeneratedRowDataFamily m gap t).rows.AdditiveEliminationConditions
        (maskGeneratedMaster m gap) w (masterColumnCoefficient N a (fun w => (C w).block) w) x
        (maskGeneratedRowDataFamily m gap t).target,
        additiveData gap a C t w x = H.data := by
  filter_upwards [maskGenerated_additive_elimination_data m gap a ha C hC] with w hw
  intro x hx
  exact additiveData_certificate gap a C t w x (hw t x hx.2)

noncomputable def rowMajorant (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (w : ℕ) (base : MaskOriginalBaseRow m gap t) (y : ℤ) : ℝ :=
  1 + integerDivisorMask (tailMass (primorial w)
    ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w base))) y

include hC in
theorem rowMajorant_eventually_nonneg (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1)) :
    ∀ᶠ w in atTop, ∀ base y, 0 ≤ rowMajorant gap C t label w base y := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  filter_upwards [hF.raw_cutoffs_valid] with w hw
  intro base y
  let Xs := (C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w base)
  have hv : ValidCutoffs Xs (primorial w) := chain_tailCutoffs_valid (C w)
    ((maskGeneratedMaster m gap).cutoff w) (primorial w) (hC w)
    (fun j hj => ⟨(hw j hj).1, (hw j hj).2.1⟩) (label w base)
  have hν := expectation_nonneg (tailMass (primorial w) Xs)
    (fun k => if (k : ℤ) ∣ y then (k : ℝ) else 0)
    (tailMass_nonneg (primorial_pos w) Xs hv) (fun _ => by split_ifs <;> positivity)
  exact add_nonneg (by norm_num) hν

noncomputable def completedMajorant (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (w : ℕ) (p : MaskOriginalPoint m gap t) (base : MaskOriginalBaseRow m gap t) (y : ℤ) : ℝ :=
  if maskGeneratedCopiedPrimeGood m gap t w p.1 then rowMajorant gap C t label w base y else 1

noncomputable def completedTest
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (w : ℕ) (p : MaskOriginalPoint m gap t) (base : MaskOriginalBaseRow m gap t) (y : ℤ) : ℝ :=
  if maskGeneratedCopiedPrimeGood m gap t w p.1 then F w p.1 base y else 0

theorem completed_test_bound
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (w : ℕ)
    (hF : ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ k y,
      |F w x (some (additiveRowAssigned _ k)) y| ≤ rowMajorant gap C t label w
        (some (additiveRowAssigned _ k)) y) :
    ∀ p k y, |completedTest gap t F w p (some (additiveRowAssigned _ k)) y| ≤
      completedMajorant gap C t label w p (some (additiveRowAssigned _ k)) y := by
  intro p k y
  unfold completedTest completedMajorant
  split_ifs with hp
  · exact hF p.1 hp k y
  · norm_num

include hC in
theorem completed_majorant_eventually_nonneg
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1)) :
    ∀ᶠ w in atTop, ∀ p base y, 0 ≤ completedMajorant gap C t label w p base y := by
  filter_upwards [rowMajorant_eventually_nonneg gap C hC t label] with w hw
  intro p base y
  unfold completedMajorant
  split_ifs
  · exact hw base y
  · norm_num

end MaskOriginalSampling
end Hindman168
