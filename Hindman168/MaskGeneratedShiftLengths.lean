import Hindman168.PredictionQuotientLengths
import Hindman168.MaskGeneratedUniformDirectionBounds
import Hindman168.MaskGeneratedCopiedMeanOne

/-! The paper's actual common shift length R/(J M(p)). A fixed exponent
bounds its prime-dependent denominator, and the actual master gap supplies
a uniform lower length and every-power growth for each fixed positive J. -/

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

namespace PolynomialRowFamily

variable {n r m : ℕ}

theorem translationModulus_polynomial_cap
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w J B : ℕ) (x : Fin n → ℕ) (target : Fin r)
    (hB : 2 ≤ B) (hM : (master.modulus w : ℕ) ≤ B) (hx : ∀ j, x j ≤ B) :
    J * F.translationModulus master w x target ≤ B ^ (J + F.translationSizeExponent target) := by
  have h := predictionCubeModulus_polynomial_cap w (master.modulus w) J B
    (F.denominator target) x hB hM (fun j _ => hx j)
  rw [predictionCubeModulus_natAbs] at h
  change J * F.translationModulus master w x target ≤ _ at h
  exact h.trans (Nat.pow_le_pow_right (by omega) (by unfold translationSizeExponent; omega))

end PolynomialRowFamily

noncomputable def maskGeneratedShiftLength (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) (J w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) : ℕ :=
  (maskGeneratedMaster m gap).gap w (gap w).val /
    (J * (maskGeneratedRowDataFamily m gap t).rows.translationModulus
      (maskGeneratedMaster m gap) w x (maskGeneratedRowDataFamily m gap t).target)

noncomputable def maskGeneratedShiftLower (m : ℕ) {N : ℕ} (gap : ℕ → Fin N) (J w : ℕ) : ℕ :=
  masterShiftLengthLowerBound (maskGeneratedMaster m gap) w (gap w).val
    (J + maskRowDirectionSizeExponent m)

theorem maskGenerated_translation_modulus_cap (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) (J w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ)
    (hx : x ∈ (masterPrimeSlotsMass (maskGeneratedMaster m gap) w (fun _ => (gap w).val)).support) :
    J * (maskGeneratedRowDataFamily m gap t).rows.translationModulus
      (maskGeneratedMaster m gap) w x (maskGeneratedRowDataFamily m gap t).target ≤
      (((maskGeneratedMaster m gap).pool w (gap w).val).upper +
        (maskGeneratedMaster m gap).auxiliary w (gap w).val) ^ (J + maskRowDirectionSizeExponent m) := by
  let B := ((maskGeneratedMaster m gap).pool w (gap w).val).upper +
    (maskGeneratedMaster m gap).auxiliary w (gap w).val
  have hB : 2 ≤ B := by
    have hh := (maskGeneratedMaster m gap).auxiliary_ge_two w (gap w).val
    dsimp [B]; omega
  have hM : ((maskGeneratedMaster m gap).modulus w : ℕ) ≤ B := by
    have hh := (maskGeneratedMaster m gap).modulus_le_auxiliary w (gap w).val
    dsimp [B]; omega
  have hpool : x ∈ (primeIndependentMass (maskGeneratedRowDataFamily m gap t).arity
      ((maskGeneratedMaster m gap).pool w (gap w).val).lower
      ((maskGeneratedMaster m gap).pool w (gap w).val).upper).support := hx
  have hxp : ∀ j, x j ≤ B := by
    intro j
    have hh := (primePool_mem.mp (primeIndependentMass_support_pool hpool j)).2.1
    dsimp [B]; omega
  exact ((maskGeneratedRowDataFamily m gap t).rows.translationModulus_polynomial_cap
    (maskGeneratedMaster m gap) w J B x _ hB hM hxp).trans
    (Nat.pow_le_pow_right (by omega) (Nat.add_le_add_left
      (maskGenerated_direction_exponent_le m gap t) J))

theorem maskGeneratedShiftLower_le_length (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J) (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ)
    (hx : maskGeneratedCopiedPrimeGood m gap t w x) :
    maskGeneratedShiftLower m gap J w ≤ maskGeneratedShiftLength m gap t J w x := by
  exact masterShiftLengthLowerBound_le_actual (maskGeneratedMaster m gap) w (gap w).val
    (J + maskRowDirectionSizeExponent m) J _
    (Nat.mul_pos hJ ((maskGeneratedRowDataFamily m gap t).rows.translationModulus_pos
      (maskGeneratedMaster m gap) w x _ hx.2))
    (maskGenerated_translation_modulus_cap m gap t J w x hx.1)

theorem maskGeneratedShiftLower_growth (m : ℕ) {N : ℕ} (gap : ℕ → Fin N) (J : ℕ) :
    PowerDominates atTop (fun w => (maskGeneratedShiftLower m gap J w : ℝ))
      (fun w => (((maskGeneratedMaster m gap).pool w (gap w).val).upper +
        (maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ)) := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  exact hF.quotient_shift_growth gap (J + maskRowDirectionSizeExponent m)

theorem maskGeneratedShiftLower_eventually_pos (m : ℕ) {N : ℕ} (gap : ℕ → Fin N) (J : ℕ) :
    ∀ᶠ w in atTop, 0 < maskGeneratedShiftLower m gap J w := by
  have h := (maskGeneratedShiftLower_growth m gap J).eventually_bound
    (Eventually.of_forall (fun _ => Nat.cast_nonneg _))
    (Eventually.of_forall (fun _ => by positivity)) 0 (by norm_num : (0 : ℝ) < 1)
  filter_upwards [h] with w hw
  simp only [pow_zero, mul_one] at hw
  have hn : 1 ≤ maskGeneratedShiftLower m gap J w := by exact_mod_cast hw
  omega

theorem maskGeneratedShiftLength_eventually_pos (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J) :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      0 < maskGeneratedShiftLength m gap t J w x := by
  filter_upwards [maskGeneratedShiftLower_eventually_pos m gap J] with w hw
  intro x hx
  exact hw.trans_le (maskGeneratedShiftLower_le_length m gap t J hJ w x hx)

theorem maskGeneratedShiftLength_displacement (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) (J w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) (hJ : 1 ≤ J) :
    (maskGeneratedRowDataFamily m gap t).rows.translationModulus (maskGeneratedMaster m gap)
      w x (maskGeneratedRowDataFamily m gap t).target * maskGeneratedShiftLength m gap t J w x ≤
      (maskGeneratedMaster m gap).gap w (gap w).val :=
  actual_shift_modulus_length_bound _ J _ hJ

end Hindman168
