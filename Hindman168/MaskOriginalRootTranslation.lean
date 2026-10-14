import Hindman168.MaskOriginalTranslationError

/-! The actual root direction annihilates the target cube. Root sampling
uses the original master gap, and its lattice displacement and polynomial
size budget are derived from the generated integer direction certificate. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskOriginalSampling

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m)))

noncomputable def rootDirection (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) (col : Fin (m + 1)) : ℤ :=
  (maskGeneratedRowDataFamily m gap t).rows.rootIntegerTranslation (maskGeneratedMaster m gap) w
    (masterColumnCoefficient N a (fun w => (C w).block) w) x
    (maskGeneratedRowDataFamily m gap t).target col

noncomputable def rootShift (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) (u₀ : ℤ) (col : Fin (m + 1)) : ℤ :=
  u₀ * rootDirection gap a C t w x col

noncomputable def rootShiftCap (w : ℕ) : ℕ :=
  (maskGeneratedMaster m gap).gap w (gap w).val *
    (((maskGeneratedMaster m gap).pool w (gap w).val).upper +
      (maskGeneratedMaster m gap).auxiliary w (gap w).val) ^ maskRowDirectionSizeExponent m

noncomputable def rootMass (w : ℕ) : Mass ℤ :=
  uniformIntervalMass 0 ((maskGeneratedMaster m gap).gap w (gap w).val)

theorem rootMass_probability (w : ℕ) :
    (∀ u₀, 0 ≤ rootMass (m := m) gap w u₀) ∧ total (rootMass (m := m) gap w) = 1 := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  exact ⟨uniformIntervalMass_nonneg _ _, uniformIntervalMass_total 0 (hF.gap_positive w _)⟩

theorem rootMass_support_natAbs_le_gap (w : ℕ) (u₀ : ℤ)
    (hu : u₀ ∈ (rootMass (m := m) gap w).support) :
    u₀.natAbs ≤ (maskGeneratedMaster m gap).gap w (gap w).val := by
  have hb := uniformIntervalMass_support_bounds 0
    ((maskGeneratedMaster m gap).gap w (gap w).val) hu
  have hn : (u₀.natAbs : ℤ) ≤ (maskGeneratedMaster m gap).gap w (gap w).val := by
    rw [Int.natCast_natAbs, abs_of_nonneg hb.1]
    simpa only [zero_add] using hb.2.le
  exact_mod_cast hn

include ha hC in
theorem rootShift_W_eventually :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ u₀ col,
      (primorial w : ℤ) ∣ rootShift gap a C t w x u₀ col := by
  filter_upwards [maskGenerated_integer_translation_conditions m gap a ha
    (fun w => (C w).block) hC (fun w col => (C w).block_nonempty col)] with w hw
  intro x hx u₀ col
  exact dvd_mul_of_dvd_right ((hw t x hx.2).root_W col) u₀

include ha hC in
theorem rootShift_size_eventually :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ u₀,
      u₀ ∈ (rootMass (m := m) gap w).support → ∀ col,
        (rootShift gap a C t w x u₀ col).natAbs ≤ rootShiftCap (m := m) gap w := by
  filter_upwards [maskGenerated_uniform_integer_translation_size_bounds m gap a ha
    (fun w => (C w).block) hC (fun w col => (C w).block_nonempty col)] with w hw
  intro x hx u₀ hu col
  rw [rootShift, Int.natAbs_mul]
  exact Nat.mul_le_mul (rootMass_support_natAbs_le_gap gap w u₀ hu) (hw t x hx.1 (maskGeneratedRowDataFamily m gap t).target col).2

include hC in
theorem rootShift_sampling_growth
    (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col) (col : Fin (m + 1)) :
    PowerDominates atTop (fun w => ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col) : ℝ))
      (fun w => (samplingSize (primorial w) 0 (rootShiftCap (m := m) gap w)
        ((maskGeneratedMaster m gap).auxiliary w (gap w).val) : ℝ)) := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  let pivot : ℕ → Fin N := fun w =>
    ⟨(C w).pivot col, Finset.mem_range.mp (hC w col (by simp [Chain.block]))⟩
  simpa only [rootShiftCap, pivot, one_mul] using hF.earlier_polynomial_translation_growth gap pivot 1
    (maskRowDirectionSizeExponent m) (hgap.mono (fun w hw => hw col))

include ha hC in
theorem root_target_form_eventually :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ z u₀,
      (maskGeneratedRowDataFamily m gap t).rows.normalizedIntegerLinearForm x
        (masterColumnCoefficient N a (fun w => (C w).block) w)
        (maskGeneratedRowDataFamily m gap t).target
        (fun col => z col + rootShift gap a C t w x u₀ col) =
      (maskGeneratedRowDataFamily m gap t).rows.normalizedIntegerLinearForm x
        (masterColumnCoefficient N a (fun w => (C w).block) w)
        (maskGeneratedRowDataFamily m gap t).target z := by
  filter_upwards [maskGenerated_chain_integer_row_directions m gap a ha C hC] with w hd
  intro x hx z u₀
  have hpool : x ∈ (primeIndependentMass (maskGeneratedRowDataFamily m gap t).arity
      ((maskGeneratedMaster m gap).pool w (gap w).val).lower
      ((maskGeneratedMaster m gap).pool w (gap w).val).upper).support := hx.1
  let coeff : Fin (m + 1) → ℤ := fun col =>
    (maskGeneratedRowDataFamily m gap t).rows.normalizedIntegerRow x
      (masterColumnCoefficient N a (fun w => (C w).block) w)
      (maskGeneratedRowDataFamily m gap t).target col
  have hz : (∑ col : Fin (m + 1), coeff col * rootDirection gap a C t w x col) = 0 :=
    (hd t x hpool hx.2).root_target_response
  change (∑ col : Fin (m + 1), coeff col *
    (z col + u₀ * rootDirection gap a C t w x col)) = ∑ col, coeff col * z col
  calc
    _ = (∑ col, coeff col * z col) + u₀ *
        ∑ col, coeff col * rootDirection gap a C t w x col := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro col _
      ring
    _ = _ := by rw [hz, mul_zero, add_zero]

include ha hC in
theorem targetCube_root_shift_eventually
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ) :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ z v u₀,
      targetCube gap a C t F w (x, fun col => z col + rootShift gap a C t w x u₀ col) v =
        targetCube gap a C t F w (x, z) v := by
  filter_upwards [root_target_form_eventually gap a ha C hC t] with w hw
  intro x hx z v u₀
  unfold targetCube
  apply Fintype.prod_congr
  intro η
  exact congrArg (fun y : ℤ => F w x none (y +
    ((maskGeneratedRowDataFamily m gap t).rows.translationModulus (maskGeneratedMaster m gap) w x
      (maskGeneratedRowDataFamily m gap t).target : ℤ) * ∑ k, predictionPairValues v k (η k)))
    (hw x hx z u₀)

end Hindman168.MaskOriginalSampling
