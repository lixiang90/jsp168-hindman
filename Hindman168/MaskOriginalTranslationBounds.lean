import Hindman168.MaskOriginalRetainedCorrelation
import Hindman168.MasterPolynomialTranslationGrowth
import Hindman168.FiniteCoordinateTranslation

/-! The actual inserted displacement is a W-lattice translation, uniformly
bounded on the original supported good tuples and actual quotient-interval
samples. Actual varying pivot cutoffs dominate its sampling budget. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskOriginalSampling

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)

noncomputable def insertionShift (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ)
    (u : MaskOriginalDirection m gap t → ℤ) (col : Fin (m + 1)) : ℤ :=
  ∑ k, u k * (maskGeneratedRowDataFamily m gap t).rows.integerTranslation
    (maskGeneratedMaster m gap) w (masterColumnCoefficient N a (fun w => (C w).block) w) x
    (maskGeneratedRowDataFamily m gap t).target
    (PolynomialRowFamily.additiveIndexEquiv (maskGeneratedRowDataFamily m gap t).target
      (some (additiveRowAssigned _ k))) col

noncomputable def insertionShiftCap (w : ℕ) : ℕ :=
  maskRowCountBound m * (maskGeneratedMaster m gap).gap w (gap w).val *
    (((maskGeneratedMaster m gap).pool w (gap w).val).upper +
      (maskGeneratedMaster m gap).auxiliary w (gap w).val) ^ maskRowDirectionSizeExponent m

theorem shiftLength_le_gap (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) :
    maskGeneratedShiftLength m gap t J w x ≤ (maskGeneratedMaster m gap).gap w (gap w).val :=
  Nat.div_le_self _ _

theorem completedDirectionMass_eq_good (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ)
    (hx : maskGeneratedCopiedPrimeGood m gap t w x) (z : Fin (m + 1) → ℤ)
    (k : MaskOriginalDirection m gap t) :
    completedDirectionMass gap a ha C hC t J hJ hgap w (x, z) k =
      uniformIntervalMass 0 (maskGeneratedShiftLength m gap t J w x) := by
  unfold completedDirectionMass eventCompletedDirectionMass
  exact if_pos hx

theorem supported_direction_natAbs_le_gap (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ)
    (hx : maskGeneratedCopiedPrimeGood m gap t w x) (z : Fin (m + 1) → ℤ)
    (u : MaskOriginalDirection m gap t → ℤ)
    (hu : u ∈ (piMass (completedDirectionMass gap a ha C hC t J hJ hgap w (x, z))).support) :
    ∀ k, (u k).natAbs ≤ (maskGeneratedMaster m gap).gap w (gap w).val := by
  intro k
  have he : (fun j : MaskOriginalDirection m gap t =>
      completedDirectionMass gap a ha C hC t J hJ hgap w (x, z) j) =
      (fun _j : MaskOriginalDirection m gap t =>
        uniformIntervalMass 0 (maskGeneratedShiftLength m gap t J w x)) :=
    funext (fun j => completedDirectionMass_eq_good gap a ha C hC t J hJ hgap w x hx z j)
  have hu' := (congrArg (fun f : MaskOriginalDirection m gap t → Mass ℤ =>
    u ∈ (piMass f).support) he).mp hu
  have hnprod := Finsupp.mem_support_iff.mp hu'
  change (∏ j : MaskOriginalDirection m gap t,
    uniformIntervalMass 0 (maskGeneratedShiftLength m gap t J w x) (u j)) ≠ 0 at hnprod
  have huk := Finsupp.mem_support_iff.mpr
    (Finset.prod_ne_zero_iff.mp hnprod k (Finset.mem_univ k))
  have hb := uniformIntervalMass_support_bounds 0 (maskGeneratedShiftLength m gap t J w x) huk
  have hab : ((u k).natAbs : ℤ) ≤ maskGeneratedShiftLength m gap t J w x := by
    rw [Int.natCast_natAbs, abs_of_nonneg hb.1]
    simpa only [zero_add] using hb.2.le
  have hn : (u k).natAbs ≤ maskGeneratedShiftLength m gap t J w x := by exact_mod_cast hab
  exact hn.trans (shiftLength_le_gap gap t J w x)

include ha hC in
theorem insertionShift_W_eventually :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ u col,
      (primorial w : ℤ) ∣ insertionShift gap a C t w x u col := by
  filter_upwards [maskGenerated_integer_translation_conditions m gap a ha
    (fun w => (C w).block) hC (fun w col => (C w).block_nonempty col)] with w hw
  intro x hx u col
  unfold insertionShift
  exact Finset.dvd_sum (fun k _ => dvd_mul_of_dvd_right
    ((hw t x hx.2).translation_W _ col) _)

include ha hC in
theorem insertionShift_size_eventually :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      ∀ u : MaskOriginalDirection m gap t → ℤ,
      (∀ k, (u k).natAbs ≤ (maskGeneratedMaster m gap).gap w (gap w).val) → ∀ col,
      (insertionShift gap a C t w x u col).natAbs ≤ insertionShiftCap (m := m) gap w := by
  filter_upwards [maskGenerated_uniform_integer_translation_size_bounds m gap a ha
    (fun w => (C w).block) hC (fun w col => (C w).block_nonempty col)] with w hw
  intro x hx u hu col
  let R := (maskGeneratedMaster m gap).gap w (gap w).val
  let B := ((maskGeneratedMaster m gap).pool w (gap w).val).upper +
    (maskGeneratedMaster m gap).auxiliary w (gap w).val
  let d := Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target)
  have hd : d ≤ maskRowCountBound m := maskGenerated_additive_dimension_le m gap t
  unfold insertionShift insertionShiftCap
  calc
    _ ≤ ∑ k : MaskOriginalDirection m gap t, (u k *
      (maskGeneratedRowDataFamily m gap t).rows.integerTranslation (maskGeneratedMaster m gap) w
        (masterColumnCoefficient N a (fun w => (C w).block) w) x
        (maskGeneratedRowDataFamily m gap t).target
        (PolynomialRowFamily.additiveIndexEquiv (maskGeneratedRowDataFamily m gap t).target
          (some (additiveRowAssigned _ k))) col).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ _k : MaskOriginalDirection m gap t, R * B ^ maskRowDirectionSizeExponent m := by
      apply Finset.sum_le_sum
      intro k _
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul (hu k) (hw t x hx.1 _ col).1
    _ = d * R * B ^ maskRowDirectionSizeExponent m := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      simp only [d, Nat.mul_assoc]
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right R hd)

include hC in
theorem insertionShift_sampling_growth
    (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col) (col : Fin (m + 1)) :
    PowerDominates atTop (fun w => ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col) : ℝ))
      (fun w => (samplingSize (primorial w) 0 (insertionShiftCap (m := m) gap w)
        ((maskGeneratedMaster m gap).auxiliary w (gap w).val) : ℝ)) := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  let pivot : ℕ → Fin N := fun w =>
    ⟨(C w).pivot col, Finset.mem_range.mp (hC w col (by simp [Chain.block]))⟩
  exact hF.earlier_polynomial_translation_growth gap pivot (maskRowCountBound m)
    (maskRowDirectionSizeExponent m) (hgap.mono (fun w hw => hw col))

end Hindman168.MaskOriginalSampling
