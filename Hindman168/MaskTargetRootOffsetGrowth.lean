import Hindman168.MaskTargetRootOffsetBounds

/-! Original logarithmic master separation makes the actual supported affine
root error rapidly small. The explicit cap includes all earlier harmonic
coordinates and actual quotient direction pairs. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskOriginalSampling

open Filter Asymptotics
open scoped Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (C : ℕ → Chain (m + 1))
  (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m)))

noncomputable def rootOffsetGrowthExponent : ℕ :=
  max (targetRootRowExponent gap t) (targetRootDenExponent gap t) + 2

noncomputable def rootOffsetGrowthConstant : ℕ :=
  m + 1 + Fintype.card (MaskOriginalDirection m gap t)

theorem rootOffsetGrowthConstant_pos : 0 < rootOffsetGrowthConstant gap t := by
  unfold rootOffsetGrowthConstant
  omega

include hC in
theorem targetRootOffsetCap_polynomial
    (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col) :
    ∀ᶠ w in atTop, targetRootMultiplierCap gap t w ≤
      (maskGeneratedMaster m gap).gap w ((C w).pivot (targetRootAnchor gap t)) ^ rootOffsetGrowthExponent gap t ∧
      targetRootOffsetCap gap C t w ≤ rootOffsetGrowthConstant gap t *
        (maskGeneratedMaster m gap).gap w ((C w).pivot (targetRootAnchor gap t)) ^ rootOffsetGrowthExponent gap t := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  have hpool := hF.indexed_pool_auxiliary_le_gap gap
  have haux := hF.auxiliary_le_gap_eventually gap
  have hauxPivot : ∀ᶠ w in atTop, ∀ col : Fin (m + 1),
      (maskGeneratedMaster m gap).auxiliary w ((C w).pivot col) ≤
        (maskGeneratedMaster m gap).gap w ((C w).pivot col) := by
    apply eventually_all.mpr
    intro col
    let pivot : ℕ → Fin N := fun w =>
      ⟨(C w).pivot col, Finset.mem_range.mp (hC w col (by simp [Chain.block]))⟩
    exact hF.auxiliary_le_gap_eventually pivot
  filter_upwards [hgap, hpool, haux, hauxPivot] with w ho hp hv hpa
  let R := (maskGeneratedMaster m gap).gap w ((C w).pivot (targetRootAnchor gap t))
  let B := rootPoolBudget (m := m) gap w
  let V := (maskGeneratedMaster m gap).auxiliary w (gap w).val
  let Vstar := (maskGeneratedMaster m gap).auxiliary w ((C w).pivot (targetRootAnchor gap t))
  let Rgap := (maskGeneratedMaster m gap).gap w (gap w).val
  have hR : 1 ≤ R := hF.gap_positive w _
  have hg : Rgap ≤ R := hF.gap_monotone w (ho _)
  have hB : B ≤ R := hp.trans hg
  have hV : V ≤ R := hv.trans hg
  have hVs : Vstar ≤ R := hpa _
  have hrE : targetRootRowExponent gap t + 2 ≤ rootOffsetGrowthExponent gap t := by
    unfold rootOffsetGrowthExponent
    omega
  have hdE : targetRootDenExponent gap t + 2 ≤ rootOffsetGrowthExponent gap t := by
    unfold rootOffsetGrowthExponent
    omega
  have hrow : V * B ^ targetRootRowExponent gap t * Vstar ≤ R ^ rootOffsetGrowthExponent gap t := by
    calc
      _ ≤ R * R ^ targetRootRowExponent gap t * R := Nat.mul_le_mul (Nat.mul_le_mul hV (Nat.pow_le_pow_left hB _)) hVs
      _ = R ^ (targetRootRowExponent gap t + 2) := by simp only [pow_add, pow_two]; ring
      _ ≤ _ := Nat.pow_le_pow_right (by omega) hrE
  have hden : V * B ^ targetRootDenExponent gap t * Rgap ≤ R ^ rootOffsetGrowthExponent gap t := by
    calc
      _ ≤ R * R ^ targetRootDenExponent gap t * R := Nat.mul_le_mul (Nat.mul_le_mul hV (Nat.pow_le_pow_left hB _)) hg
      _ = R ^ (targetRootDenExponent gap t + 2) := by simp only [pow_add, pow_two]; ring
      _ ≤ _ := Nat.pow_le_pow_right (by omega) hdE
  constructor
  · have hk := targetRootMultiplierExponent_le_rowExponent gap t
    exact (Nat.pow_le_pow_left hB _).trans
      (Nat.pow_le_pow_right (by omega) (hk.trans (by omega : targetRootRowExponent gap t ≤ rootOffsetGrowthExponent gap t)))
  · change (m + 1) * (V * B ^ targetRootRowExponent gap t * Vstar) +
      Fintype.card (MaskOriginalDirection m gap t) * (V * B ^ targetRootDenExponent gap t) * Rgap ≤ _
    calc
      _ ≤ (m + 1) * R ^ rootOffsetGrowthExponent gap t +
        Fintype.card (MaskOriginalDirection m gap t) * R ^ rootOffsetGrowthExponent gap t :=
          add_le_add (Nat.mul_le_mul_left _ hrow)
            (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (Fintype.card (MaskOriginalDirection m gap t)) hden)
      _ = _ := by unfold rootOffsetGrowthConstant; ring

include hC in
theorem targetRootOffset_sampling_log_growth
    (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col) :
    PowerDominates atTop (fun w => Real.log
      ((maskGeneratedMaster m gap).cutoff w ((C w).pivot (targetRootAnchor gap t)) : ℝ))
      (fun w => (samplingSize (primorial w) (targetRootMultiplierCap gap t w)
        (targetRootOffsetCap gap C t w) ((maskGeneratedMaster m gap).auxiliary w (gap w).val) : ℝ)) := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  let pivot : ℕ → Fin N := fun w =>
    ⟨(C w).pivot (targetRootAnchor gap t), Finset.mem_range.mp (hC w (targetRootAnchor gap t) (by simp [Chain.block]))⟩
  apply hF.polynomial_gap_affine_log_growth pivot (rootOffsetGrowthConstant gap t) (rootOffsetGrowthExponent gap t)
  · filter_upwards [targetRootOffsetCap_polynomial gap C hC t hgap] with w hw
    exact hw.1.trans (Nat.le_mul_of_pos_left _ (rootOffsetGrowthConstant_pos gap t))
  · exact (targetRootOffsetCap_polynomial gap C hC t hgap).mono (fun _ hw => hw.2)
  · exact hgap.mono (fun w hw => hF.auxiliary_monotone w (hw _))

noncomputable def targetRootAffineErrorCap (w : ℕ) : ℝ :=
  affineRootErrorCap ((maskGeneratedMaster m gap).cutoff w ((C w).pivot (targetRootAnchor gap t)))
    (primorial w) (targetRootMultiplierCap gap t w) (targetRootOffsetCap gap C t w)
    ((maskGeneratedMaster m gap).auxiliary w (gap w).val)

include hC in
theorem targetRootAffineErrorCap_rapid
    (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col) :
    RapidlySmall atTop (fun w => ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ))
      (targetRootAffineErrorCap gap C t) :=
  affineRootErrorCap_rapid (targetRootOffset_sampling_log_growth gap C hC t hgap)
    (Eventually.of_forall (fun w => (by decide : 1 ≤ 2).trans
      ((maskGeneratedMaster m gap).auxiliary_ge_two w (gap w).val)))

end Hindman168.MaskOriginalSampling
