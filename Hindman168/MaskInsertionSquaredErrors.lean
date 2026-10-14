import Hindman168.MaskStageCorrelationInputs

/-! Polynomially weighted insertion errors and square transfer. The
fixed master variance and dilation caps derive the decay needed after
squaring a polynomially bounded original correlation. -/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical

noncomputable def maskSquareInsertionLoss (V e : ℝ) (B : ℕ) : ℝ := 2 * V ^ B * |e|

theorem abs_square_le_square_add_twice_cap_error (x y K e : ℝ)
    (hK : |x| ≤ K) (he : |x - y| ≤ e) :
    |x| ^ 2 ≤ |y| ^ 2 + 2 * K * e := by
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  have hK0 : 0 ≤ K := (abs_nonneg _).trans hK
  by_cases hxy : |x| ≤ |y|
  · have hs := pow_le_pow_left₀ (abs_nonneg x) hxy 2
    nlinarith
  · have hd : |x| - |y| ≤ e := by
      have ht := abs_add_le (x-y) y
      rw [sub_add_cancel] at ht
      linarith
    have hsum : |x| + |y| ≤ 2*K := by linarith
    have hm := mul_le_mul hd hsum (add_nonneg (abs_nonneg x) (abs_nonneg y)) he0
    nlinarith

theorem masterPrimeInsertionErrorCap_weighted_identity (F : MasterParameterFamily)
    {N : ℕ} (gap pivot : ℕ → Fin N) (B D w : ℕ) :
    (F.auxiliary w (gap w).val : ℝ) ^ D * masterPrimeInsertionErrorCap F gap pivot B w =
      masterPrimeInsertionErrorCap F gap pivot (B + D) w := by
  let V : ℝ := F.auxiliary w (gap w).val
  have hv : 0 ≤ V := by dsimp [V]; positivity
  have hs : V ^ (2 * (B+D)) * masterPrimeInsertionVarianceCap F gap pivot w =
      (V ^ D) ^ 2 * (V ^ (2*B) * masterPrimeInsertionVarianceCap F gap pivot w) := by
    rw [← pow_mul, ← mul_assoc, ← pow_add]
    rw [show 2 * (B + D) = D * 2 + 2 * B by omega]
  unfold masterPrimeInsertionErrorCap
  change V ^ D * (Real.sqrt (V ^ (2*B) * masterPrimeInsertionVarianceCap F gap pivot w) +
    V ^ B * masterPrimePairDilationErrorCap F gap pivot w) =
    Real.sqrt (V ^ (2*(B+D)) * masterPrimeInsertionVarianceCap F gap pivot w) +
      V ^ (B+D) * masterPrimePairDilationErrorCap F gap pivot w
  rw [mul_add, hs, Real.sqrt_mul (sq_nonneg (V^D)), Real.sqrt_sq_eq_abs,
    abs_of_nonneg (pow_nonneg hv D)]
  congr 1
  rw [← mul_assoc, ← pow_add, Nat.add_comm D B]

variable {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)}
  {F : MasterParameterFamily} (hF : MasterParameterConditions N A D F)
  (gap pivot : ℕ → Fin N) (horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val)

include hF horder in
theorem MasterParameterConditions.prime_insertion_weighted_error_tendsto (B L : ℕ) :
    Tendsto (fun w => (F.auxiliary w (gap w).val : ℝ) ^ L *
      masterPrimeInsertionErrorCap F gap pivot B w) atTop (𝓝 0) := by
  simp_rw [masterPrimeInsertionErrorCap_weighted_identity]
  exact hF.prime_insertion_error_cap_tendsto gap pivot horder (B+L)

namespace MaskColumnPlan

variable {m N : ℕ} {S U : Finset (Fin (m + 1))}

noncomputable def insertionErrorCap (P : MaskColumnPlan S U) (gap : ℕ → Fin N)
    (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N) (B w : ℕ) : ℝ :=
  match P with
  | .outside u _ _ => masterPrimeInsertionErrorCap (maskGeneratedMaster m gap) gap
      (maskOriginalPivotIndex C hC u) B w
  | .balanced u v _ _ _ _ _ => maskBalancedPrimeInsertionErrorCap gap C hC u v B w

end MaskColumnPlan

variable {m : ℕ} (C : ℕ → Chain (m + 1))
  (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)

include hgap in
theorem maskBalancedInsertionErrorCap_weighted_tendsto (u v : Fin (m + 1)) (B L : ℕ) :
    Tendsto (fun w => ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ)^L *
      maskBalancedPrimeInsertionErrorCap gap C hC u v B w) atTop (𝓝 0) := by
  have hc := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  have ht := (hc.prime_insertion_weighted_error_tendsto gap (maskOriginalPivotIndex C hC v)
    (hgap.mono (fun w hw => hw v)) B L).add
    (hc.prime_pair_dilation_weighted_cap_tendsto gap (maskOriginalPivotIndex C hC u)
      (hgap.mono (fun w hw => hw u)) (B+L))
  simpa only [maskBalancedPrimeInsertionErrorCap, mul_add, ← mul_assoc, ← pow_add,
    Nat.add_comm L B, zero_add] using ht

include hgap in
theorem maskPlanInsertionErrorCap_weighted_tendsto {S U : Finset (Fin (m + 1))}
    (P : MaskColumnPlan S U) (B L : ℕ) :
    Tendsto (fun w => ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ)^L *
      P.insertionErrorCap gap C hC B w) atTop (𝓝 0) := by
  have hc := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  cases P with
  | outside u hu hU =>
    exact hc.prime_insertion_weighted_error_tendsto gap (maskOriginalPivotIndex C hC u)
      (hgap.mono (fun w hw => hw u)) B L
  | balanced u v hu hv huU hvU hne =>
    exact maskBalancedInsertionErrorCap_weighted_tendsto gap C hC hgap u v B L

include hgap in
theorem maskPlanSquaredInsertionLoss_tendsto {S U : Finset (Fin (m + 1))}
    (P : MaskColumnPlan S U) (B : ℕ) :
    Tendsto (fun w => maskSquareInsertionLoss
      ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) (P.insertionErrorCap gap C hC B w) B)
      atTop (𝓝 0) := by
  have ht := (maskPlanInsertionErrorCap_weighted_tendsto gap C hC hgap P B B).abs
  have he : (fun w => |((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ)^B *
      P.insertionErrorCap gap C hC B w|) =
      fun w => ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ)^B *
        |P.insertionErrorCap gap C hC B w| := by
    funext w
    rw [abs_mul, abs_of_nonneg (by positivity)]
  rw [he] at ht
  simpa only [maskSquareInsertionLoss, mul_assoc, mul_zero, abs_zero] using ht.const_mul 2

end Hindman168
