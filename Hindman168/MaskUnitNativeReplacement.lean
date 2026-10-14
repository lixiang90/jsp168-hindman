import Hindman168.MaskSubsetModelTelescoping

/-! Exact finite telescoping for the bounded F-S replacement. Every
companion factor and original product mask is retained. The total error
is the actual number of nonsingleton mask supports times the tested error. -/

namespace Hindman168
open scoped Classical
open MaskOriginalSampling

theorem maskSubsetModelReplacement_twice {m : ℕ}
    (H : NonemptyColumnSubset (m+1) → ℤ → ℝ) (F S : Fin (m+1) → ℤ → ℝ) :
    maskSubsetModelReplacement (maskSubsetModelReplacement H F) S =
      maskSubsetModelReplacement H S := by
  funext U
  by_cases h : 2 ≤ U.val.card <;> simp only [maskSubsetModelReplacement, h, ite_true, ite_false]

theorem mask_unit_native_replacement {m N : ℕ} (gap : ℕ → Fin N)
    (a : Fin (m+1) → ℚ) (C : ℕ → Chain (m+1)) (w : ℕ)
    (F S : Fin (m+1) → ℤ → ℝ)
    (hF : ∀ col y, 0 ≤ F col y ∧ F col y ≤ 1)
    (hS : ∀ col y, 0 ≤ S col y ∧ S col y ≤ 1)
    (hν : ∀ U : NonemptyColumnSubset (m+1), ∀ y, 0 ≤ maskSubsetTailMask gap C w U y)
    (ε : ℝ)
    (herror : ∀ t : Fin (Fintype.card (LargeColumnSubset m)),
      ∀ H : NonemptyColumnSubset (m+1) → ℤ → ℝ, ∀ b : Finset (Fin (m+1)) → ℤ → ℝ,
      maskOriginalSubsetAdmissible gap C w H b →
      H (maskSourceNonemptySupport m t) =
        (fun y => F (targetRootAnchor gap t) y - S (targetRootAnchor gap t) y) →
      |maskOriginalSubsetCorrelation gap a C w H b| ≤ ε)
    (H : NonemptyColumnSubset (m+1) → ℤ → ℝ) (b : Finset (Fin (m+1)) → ℤ → ℝ)
    (hH : maskOriginalSubsetAdmissible gap C w H b)
    (htarget : ∀ U : NonemptyColumnSubset (m+1), 2 ≤ U.val.card → H U = F (U.val.max' U.property)) :
    |maskOriginalSubsetCorrelation gap a C w H b -
      maskOriginalSubsetCorrelation gap a C w (maskSubsetModelReplacement H S) b| ≤
      (Fintype.card (LargeColumnSubset m) : ℝ) * ε := by
  let L := Fintype.card (LargeColumnSubset m)
  have hsteps (k : ℕ) (hk : k < L) :
      |maskOriginalSubsetCorrelation gap a C w (maskSubsetHybrid H S k) b -
        maskOriginalSubsetCorrelation gap a C w (maskSubsetHybrid H S (k+1)) b| ≤ ε := by
    let t : Fin (Fintype.card (LargeColumnSubset m)) := ⟨k, hk⟩
    let col := targetRootAnchor gap t
    have ht := htarget (maskSourceNonemptySupport m t) (maskSourceSupport_card m t)
    rw [← maskTargetRootAnchor_eq_sourceMax gap t] at ht
    have hhybrid := maskSubsetHybrid_admissible gap C w H b hH S hS hν t.val
    have he : ∀ y, |F col y - S col y| ≤ 1 +
        maskSubsetTailMask gap C w (maskSourceNonemptySupport m t) y := by
      intro y
      have hb : |F col y - S col y| ≤ 1 := abs_sub_le_iff.mpr
        ⟨by linarith [(hF col y).2, (hS col y).1], by linarith [(hS col y).2, (hF col y).1]⟩
      exact hb.trans (by linarith [hν (maskSourceNonemptySupport m t) y])
    have hu := maskOriginalSubset_update_admissible gap C w _ b hhybrid
      (maskSourceNonemptySupport m t) (fun y => F col y - S col y) he
    have hx := herror t _ b hu (by simp only [Function.update_self]; rfl)
    have hp := maskSubsetHybrid_step H S t
    rw [← maskTargetRootAnchor_eq_sourceMax gap t] at hp
    change |maskOriginalSubsetCorrelation gap a C w (maskSubsetHybrid H S t.val) b -
      maskOriginalSubsetCorrelation gap a C w (maskSubsetHybrid H S (t.val+1)) b| ≤ ε
    rw [hp, maskOriginalSubsetCorrelation_update_difference,
      maskSubsetHybrid_target_before, ht]
    exact hx
  have he := finite_difference_chain_abs_bound
    (fun k => maskOriginalSubsetCorrelation gap a C w (maskSubsetHybrid H S k) b) L ε hsteps
  simpa only [L, maskSubsetHybrid_zero, maskSubsetHybrid_full] using he

theorem mask_native_replacement_of_error_path {m N : ℕ} (gap : ℕ → Fin N)
    (a : Fin (m+1) → ℚ) (C : ℕ → Chain (m+1)) (w : ℕ)
    (H : NonemptyColumnSubset (m+1) → ℤ → ℝ) (b : Finset (Fin (m+1)) → ℤ → ℝ)
    (F S : Fin (m+1) → ℤ → ℝ)
    (htarget : ∀ U : NonemptyColumnSubset (m+1), 2 ≤ U.val.card → H U = F (U.val.max' U.property))
    (ε : ℝ)
    (herror : ∀ t : Fin (Fintype.card (LargeColumnSubset m)),
      |maskOriginalSubsetCorrelation gap a C w
        (Function.update (maskSubsetHybrid H S t.val) (maskSourceNonemptySupport m t)
          (fun y => F (targetRootAnchor gap t) y - S (targetRootAnchor gap t) y)) b| ≤ ε) :
    |maskOriginalSubsetCorrelation gap a C w H b -
      maskOriginalSubsetCorrelation gap a C w (maskSubsetModelReplacement H S) b| ≤
      (Fintype.card (LargeColumnSubset m) : ℝ) * ε := by
  let L := Fintype.card (LargeColumnSubset m)
  have hsteps (k : ℕ) (hk : k < L) :
      |maskOriginalSubsetCorrelation gap a C w (maskSubsetHybrid H S k) b -
        maskOriginalSubsetCorrelation gap a C w (maskSubsetHybrid H S (k+1)) b| ≤ ε := by
    let t : Fin (Fintype.card (LargeColumnSubset m)) := ⟨k, hk⟩
    have ht := htarget (maskSourceNonemptySupport m t) (maskSourceSupport_card m t)
    rw [← maskTargetRootAnchor_eq_sourceMax gap t] at ht
    have hp := maskSubsetHybrid_step H S t
    rw [← maskTargetRootAnchor_eq_sourceMax gap t] at hp
    change |maskOriginalSubsetCorrelation gap a C w (maskSubsetHybrid H S t.val) b -
      maskOriginalSubsetCorrelation gap a C w (maskSubsetHybrid H S (t.val+1)) b| ≤ ε
    rw [hp, maskOriginalSubsetCorrelation_update_difference, maskSubsetHybrid_target_before, ht]
    exact herror t
  have he := finite_difference_chain_abs_bound
    (fun k => maskOriginalSubsetCorrelation gap a C w (maskSubsetHybrid H S k) b) L ε hsteps
  simpa only [L, maskSubsetHybrid_zero, maskSubsetHybrid_full] using he

end Hindman168
