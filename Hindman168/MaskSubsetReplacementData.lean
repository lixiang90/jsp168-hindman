import Hindman168.MaskModelOriginalCorrelation

/-! Actual support maxima, target anchors and original majorants needed
for model replacement. The generated target retains its exact original
support throughout every mask step. -/

set_option maxHeartbeats 2000000

namespace Hindman168
open Filter
open scoped BigOperators Topology Classical
open MaskOriginalSampling

variable {m N : ℕ} (gap : ℕ → Fin N) (C : ℕ → Chain (m+1))

noncomputable def maskLargeSubsetIndex (U : NonemptyColumnSubset (m+1)) (hU : 2 ≤ U.val.card) :
    Fin (Fintype.card (LargeColumnSubset m)) := (Fintype.equivFin (LargeColumnSubset m)) ⟨U.val, hU⟩

theorem maskSourceNonemptySupport_index (U : NonemptyColumnSubset (m+1)) (hU : 2 ≤ U.val.card) :
    maskSourceNonemptySupport m (maskLargeSubsetIndex U hU) = U := by
  apply Subtype.ext
  simp [maskSourceNonemptySupport, maskSourceSupport, maskLargeSubsetIndex]

theorem maskTargetRootAnchor_eq_sourceMax (t : Fin (Fintype.card (LargeColumnSubset m))) :
    targetRootAnchor gap t = (maskSourceNonemptySupport m t).val.max'
      (maskSourceNonemptySupport m t).property := by
  let S := maskSourceNonemptySupport m t
  let F := maskSourceFullStage m t
  change F.rows.normalizationAnchor F.target = S.val.max' S.property
  apply le_antisymm
  · apply S.val.le_max'
    exact (F.target_support _).mp (F.rows.normalizationAnchor_ne_zero F.target)
  · apply F.rows.le_normalizationAnchor
    exact (F.target_support _).mpr (Finset.max'_mem _ _)

theorem maskSubsetTailMask_eq_blockMask (w : ℕ) (U : NonemptyColumnSubset (m+1)) (y : ℤ) :
    maskSubsetTailMask gap C w U y =
      masterPredictionBlockMask (maskGeneratedMaster m gap) C (fun _ => U.val.max' U.property) w y := rfl

theorem maskSourceTailMask_eq_targetBlock (t : Fin (Fintype.card (LargeColumnSubset m)))
    (w : ℕ) (y : ℤ) :
    maskSubsetTailMask gap C w (maskSourceNonemptySupport m t) y =
      masterPredictionBlockMask (maskGeneratedMaster m gap) C (fun _ => targetRootAnchor gap t) w y := by
  rw [maskSubsetTailMask_eq_blockMask, maskTargetRootAnchor_eq_sourceMax]

theorem maskSubsetTailMask_eventually_nonneg
    (hC : ∀ w col, (C w).block col ⊆ Finset.range N) :
    ∀ᶠ w in atTop, ∀ U : NonemptyColumnSubset (m+1), ∀ y, 0 ≤ maskSubsetTailMask gap C w U y := by
  apply eventually_all.mpr
  intro U
  simpa only [maskSubsetTailMask_eq_blockMask] using
    (maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)).block_mask_eventually_nonneg
      C hC (fun _ => U.val.max' U.property)

theorem maskOriginalSubset_update_admissible (w : ℕ)
    (f : NonemptyColumnSubset (m+1) → ℤ → ℝ) (b : Finset (Fin (m+1)) → ℤ → ℝ)
    (hf : maskOriginalSubsetAdmissible gap C w f b) (U : NonemptyColumnSubset (m+1))
    (g : ℤ → ℝ) (hg : ∀ y, |g y| ≤ 1 + maskSubsetTailMask gap C w U y) :
    maskOriginalSubsetAdmissible gap C w (Function.update f U g) b := by
  refine ⟨?_, hf.2⟩
  intro V y
  by_cases h : V = U
  · subst V; simpa only [Function.update_self] using hg y
  · simpa only [Function.update_of_ne h] using hf.1 V y

end Hindman168
