import Hindman168.MaskSubsetSingleReplacement

/-! A finite replacement path visits every nonsingleton subset exactly
once. All factors remain discrete original functions of their normalized
integer form; singleton factors and product masks are untouched. -/

set_option maxHeartbeats 2000000

namespace Hindman168
open scoped BigOperators Classical

variable {m N : ℕ}

theorem maskLargeSubsetIndex_source (t : Fin (Fintype.card (LargeColumnSubset m))) :
    maskLargeSubsetIndex (maskSourceNonemptySupport m t) (maskSourceSupport_card m t) = t := by
  change (Fintype.equivFin (LargeColumnSubset m))
    ((Fintype.equivFin (LargeColumnSubset m)).symm t) = t
  exact Equiv.apply_symm_apply _ t

noncomputable def maskSubsetHybrid
    (f : NonemptyColumnSubset (m+1) → ℤ → ℝ) (model : Fin (m+1) → ℤ → ℝ)
    (k : ℕ) (U : NonemptyColumnSubset (m+1)) : ℤ → ℝ :=
  if h : 2 ≤ U.val.card then
    if (maskLargeSubsetIndex U h).val < k then model (U.val.max' U.property) else f U
  else f U

noncomputable def maskSubsetModelReplacement
    (f : NonemptyColumnSubset (m+1) → ℤ → ℝ) (model : Fin (m+1) → ℤ → ℝ)
    (U : NonemptyColumnSubset (m+1)) : ℤ → ℝ :=
  if 2 ≤ U.val.card then model (U.val.max' U.property) else f U

theorem maskSubsetHybrid_zero (f : NonemptyColumnSubset (m+1) → ℤ → ℝ)
    (model : Fin (m+1) → ℤ → ℝ) : maskSubsetHybrid f model 0 = f := by
  funext U
  by_cases h : 2 ≤ U.val.card <;> simp [maskSubsetHybrid, h]

theorem maskSubsetHybrid_full (f : NonemptyColumnSubset (m+1) → ℤ → ℝ)
    (model : Fin (m+1) → ℤ → ℝ) :
    maskSubsetHybrid f model (Fintype.card (LargeColumnSubset m)) =
      maskSubsetModelReplacement f model := by
  funext U
  by_cases h : 2 ≤ U.val.card
  · simp only [maskSubsetHybrid, dif_pos h, if_pos (maskLargeSubsetIndex U h).isLt,
      maskSubsetModelReplacement, if_pos h]
  · simp only [maskSubsetHybrid, dif_neg h, maskSubsetModelReplacement, if_neg h]

theorem maskSubsetHybrid_target_before (f : NonemptyColumnSubset (m+1) → ℤ → ℝ)
    (model : Fin (m+1) → ℤ → ℝ) (t : Fin (Fintype.card (LargeColumnSubset m))) :
    maskSubsetHybrid f model t.val (maskSourceNonemptySupport m t) = f (maskSourceNonemptySupport m t) := by
  rw [maskSubsetHybrid, dif_pos (show 2 ≤ (maskSourceNonemptySupport m t).val.card from
    maskSourceSupport_card m t), maskLargeSubsetIndex_source, if_neg (lt_irrefl t.val)]

theorem maskSubsetHybrid_step (f : NonemptyColumnSubset (m+1) → ℤ → ℝ)
    (model : Fin (m+1) → ℤ → ℝ) (t : Fin (Fintype.card (LargeColumnSubset m))) :
    maskSubsetHybrid f model (t.val+1) =
      Function.update (maskSubsetHybrid f model t.val) (maskSourceNonemptySupport m t)
        (model ((maskSourceNonemptySupport m t).val.max' (maskSourceNonemptySupport m t).property)) := by
  funext U
  by_cases hU : U = maskSourceNonemptySupport m t
  · subst U
    rw [Function.update_self, maskSubsetHybrid,
      dif_pos (show 2 ≤ (maskSourceNonemptySupport m t).val.card from maskSourceSupport_card m t),
      maskLargeSubsetIndex_source, if_pos (Nat.lt_succ_self t.val)]
  · rw [Function.update_of_ne hU]
    by_cases h : 2 ≤ U.val.card
    · have hi : (maskLargeSubsetIndex U h).val ≠ t.val := by
        intro he
        have ht : maskLargeSubsetIndex U h = t := Fin.ext he
        have hu := maskSourceNonemptySupport_index U h
        rw [ht] at hu
        exact hU hu.symm
      have he : (maskLargeSubsetIndex U h).val < t.val + 1 ↔
          (maskLargeSubsetIndex U h).val < t.val := by omega
      simp only [maskSubsetHybrid, dif_pos h, he]
    · simp only [maskSubsetHybrid, dif_neg h]

theorem maskSubsetHybrid_admissible (gap : ℕ → Fin N) (C : ℕ → Chain (m+1)) (w : ℕ)
    (f : NonemptyColumnSubset (m+1) → ℤ → ℝ) (b : Finset (Fin (m+1)) → ℤ → ℝ)
    (hf : maskOriginalSubsetAdmissible gap C w f b) (model : Fin (m+1) → ℤ → ℝ)
    (hm : ∀ col y, 0 ≤ model col y ∧ model col y ≤ 1)
    (hν : ∀ U : NonemptyColumnSubset (m+1), ∀ y, 0 ≤ maskSubsetTailMask gap C w U y) (k : ℕ) :
    maskOriginalSubsetAdmissible gap C w (maskSubsetHybrid f model k) b := by
  refine ⟨?_, hf.2⟩
  intro U y
  unfold maskSubsetHybrid
  split_ifs
  · rw [abs_of_nonneg (hm _ y).1]
    exact (hm _ y).2.trans (by linarith [hν U y])
  · exact hf.1 U y
  · exact hf.1 U y

end Hindman168
