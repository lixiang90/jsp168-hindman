import Hindman168.MaskPoweredElimination
import Hindman168.MaskEndpointTargetCube

/-! Full arbitrary-target powered correlation output. The finite mask
power and the actual additive power combine; the coefficient depends
only on m, and both errors are uniform over admissible functions. -/

set_option maxHeartbeats 2000000

namespace Hindman168
open Filter
open scoped Topology Classical
open MaskOriginalSampling

noncomputable def maskFullOutputLiftCoefficient (m : ℕ) : ℝ :=
  (2 * maskRemovalPowerCoefficient m) ^ (2 ^ maskRowCountBound m)

noncomputable def maskFullOutputCoefficient (m : ℕ) : ℝ :=
  maskFullOutputLiftCoefficient m * maskAdditiveOutputBound m

theorem maskFullOutputLiftCoefficient_ge_one (m : ℕ) : 1 ≤ maskFullOutputLiftCoefficient m := by
  unfold maskFullOutputLiftCoefficient
  apply one_le_pow₀
  have h := maskRemovalPowerCoefficient_ge_one m
  linarith

theorem maskFullOutputCoefficient_ge_one (m : ℕ) : 1 ≤ maskFullOutputCoefficient m := by
  unfold maskFullOutputCoefficient
  have hl := maskFullOutputLiftCoefficient_ge_one m
  have ha := maskAdditiveOutputBound_ge_one m
  nlinarith

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m+1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m+1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
  (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)

noncomputable def maskFullCorrelationPower : ℕ :=
  2 ^ ((allNonemptyColumnMasks m).length + targetPredictionOrder gap t)

theorem maskFullCorrelationPower_pos : 0 < maskFullCorrelationPower gap t := by
  unfold maskFullCorrelationPower
  positivity

theorem maskFullCorrelationPower_le_bound :
    maskFullCorrelationPower gap t ≤
      2 ^ ((allNonemptyColumnMasks m).length + maskRowCountBound m) := by
  unfold maskFullCorrelationPower
  exact Nat.pow_le_pow_right (by decide : 0 < 2)
    (Nat.add_le_add_left (maskGenerated_additive_dimension_le m gap t) _)

theorem maskFullOutputLift_factor_bound :
    (2 : ℝ) ^ (2 ^ targetPredictionOrder gap t) *
      maskRemovalPowerCoefficient m ^ (2 ^ targetPredictionOrder gap t) ≤ maskFullOutputLiftCoefficient m := by
  rw [← mul_pow]
  unfold maskFullOutputLiftCoefficient
  apply pow_le_pow_right₀
  · have h := maskRemovalPowerCoefficient_ge_one m
    linarith
  · exact Nat.pow_le_pow_right (by decide : 0 < 2) (maskGenerated_additive_dimension_le m gap t)

include ha hC hJ hgap htail in
theorem maskFullCorrelation_output_uniform :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop, ∀ g : ℤ → ℝ,
      ∀ D : MaskStageCorrelationInput (maskSourceSupport m t) (maskSourceSupport_card m t)
        gap C 0 w (maskRemainingMasks m 0),
      maskStageInputHasTarget (maskSourceSupport m t) (maskSourceSupport_card m t) gap C D g →
      |maskStageInputCorrelation (maskSourceSupport m t) (maskSourceSupport_card m t) gap a C D| ^
        maskFullCorrelationPower gap t ≤
        maskFullOutputCoefficient m * |maskEndpointTargetCube gap C t J w g| + ε := by
  intro ε hε
  let S := maskSourceSupport m t
  let hS := maskSourceSupport_card m t
  let p := 2 ^ targetPredictionOrder gap t
  let A := maskRemovalPowerCoefficient m
  let H : ℝ := 2 ^ p * A ^ p
  have hA : 1 ≤ A := maskRemovalPowerCoefficient_ge_one m
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hp : p ≠ 0 := by dsimp only [p]; positivity
  let η := (ε / 2) / (H + 1)
  have hη : 0 < η := by dsimp only [η]; positivity
  have hH1 : H + 1 ≠ 0 := by linarith
  have hηeq : (H+1) * η = ε/2 := by dsimp only [η]; field_simp
  have hHη : H * η ≤ ε/2 := by nlinarith
  have he : Tendsto (fun w => (2 : ℝ)^p * maskOrderedPowerError S hS gap C hC w ^ p)
      atTop (𝓝 0) := by
    simpa only [zero_pow hp, mul_zero] using
      ((maskOrderedPowerError_tendsto_zero S hS gap C hC hgap).pow p).const_mul ((2 : ℝ)^p)
  filter_upwards [maskPoweredElimination_eventually S hS gap a ha C hC hgap htail,
    maskTerminal_general_additive_output_uniform gap a ha C hC t J hJ hgap htail η hη,
    he.eventually (eventually_lt_nhds (by linarith : 0 < ε/2))] with w hm ht herr
  intro g D hD
  obtain ⟨E, hE, hmask⟩ := hm g D hD
  have htarget := ht g E hE
  have hcap : 0 ≤ maskOrderedPowerError S hS gap C hC w := maskOrderedPowerError_nonneg S hS gap C hC w
  have hsum := nonnegative_add_pow_le_double
    (A * |maskStageInputCorrelation S hS gap a C E|) (maskOrderedPowerError S hS gap C hC w)
    (by positivity) hcap p
  have hcoef : H * maskAdditiveOutputBound m ≤ maskFullOutputCoefficient m := by
    exact mul_le_mul_of_nonneg_right (maskFullOutputLift_factor_bound gap t)
      ((zero_le_one : (0 : ℝ) ≤ 1).trans (maskAdditiveOutputBound_ge_one m))
  calc
    _ = (|maskStageInputCorrelation S hS gap a C D| ^ (2 ^ (allNonemptyColumnMasks m).length)) ^ p := by
      rw [← pow_mul, ← pow_add]
      rfl
    _ ≤ (A * |maskStageInputCorrelation S hS gap a C E| + maskOrderedPowerError S hS gap C hC w) ^ p :=
      pow_le_pow_left₀ (by positivity) hmask p
    _ ≤ H * |maskStageInputCorrelation S hS gap a C E| ^ p +
        (2 : ℝ)^p * maskOrderedPowerError S hS gap C hC w ^ p := by
      simpa only [H, mul_pow, mul_assoc] using hsum
    _ ≤ H * (maskAdditiveOutputBound m * |maskEndpointTargetCube gap C t J w g| + η) +
        (2 : ℝ)^p * maskOrderedPowerError S hS gap C hC w ^ p :=
      add_le_add (mul_le_mul_of_nonneg_left htarget hH) le_rfl
    _ ≤ H * maskAdditiveOutputBound m * |maskEndpointTargetCube gap C t J w g| + ε := by
      nlinarith
    _ ≤ maskFullOutputCoefficient m * |maskEndpointTargetCube gap C t J w g| + ε :=
      add_le_add (mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)) le_rfl

include ha hC hJ hgap htail in
theorem maskFullCorrelation_all_supports_output_uniform :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop, ∀ t : Fin (Fintype.card (LargeColumnSubset m)), ∀ g : ℤ → ℝ,
      ∀ D : MaskStageCorrelationInput (maskSourceSupport m t) (maskSourceSupport_card m t)
        gap C 0 w (maskRemainingMasks m 0),
      maskStageInputHasTarget (maskSourceSupport m t) (maskSourceSupport_card m t) gap C D g →
      |maskStageInputCorrelation (maskSourceSupport m t) (maskSourceSupport_card m t) gap a C D| ^
        maskFullCorrelationPower gap t ≤
        maskFullOutputCoefficient m * |maskEndpointTargetCube gap C t J w g| + ε := by
  intro ε hε
  apply eventually_all.mpr
  intro t
  exact maskFullCorrelation_output_uniform gap a ha C hC t J hJ hgap htail ε hε

end Hindman168
