import Hindman168.FinitePivotCauchySchwarz
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Finite iteration of weighted squaring bounds

For n steps with a common prefactor cap C, the exponent is exactly 2^n
on the original average and 2^n-1 on C. Separately, bounded prefactors
and a vanishing terminal average imply a vanishing original average.
These scalar statements do not assume an iteration has been connected
to the concrete prediction forms or the master interval laws.
-/

namespace Hindman168

open Filter
open scoped Topology

theorem iterated_squared_bound (n : ℕ) (A : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hstep : ∀ i < n, |A i| ^ 2 ≤ C * |A (i + 1)|) :
    |A 0| ^ (2 ^ n) ≤ C ^ (2 ^ n - 1) * |A n| := by
  induction n generalizing A with
  | zero => simp
  | succ n ih =>
    have hfirst := hstep 0 (Nat.zero_lt_succ n)
    have hpow := pow_le_pow_left₀ (sq_nonneg (|A 0|)) hfirst (2 ^ n)
    have htail := ih (fun i => A (i + 1)) (fun i hi => hstep (i + 1) (by omega))
    calc
      |A 0| ^ (2 ^ (n + 1)) = (|A 0| ^ 2) ^ (2 ^ n) := by
        rw [← pow_mul, pow_succ]
        rw [Nat.mul_comm 2]
      _ ≤ (C * |A 1|) ^ (2 ^ n) := hpow
      _ = C ^ (2 ^ n) * |A 1| ^ (2 ^ n) := mul_pow _ _ _
      _ ≤ C ^ (2 ^ n) * (C ^ (2 ^ n - 1) * |A (n + 1)|) :=
        mul_le_mul_of_nonneg_left htail (pow_nonneg hC _)
      _ = C ^ (2 ^ (n + 1) - 1) * |A (n + 1)| := by
        rw [← mul_assoc, ← pow_add]
        congr 1
        congr 1
        have hp : 0 < (2 : ℕ) ^ n := pow_pos (by omega) _
        rw [pow_succ]
        omega

theorem squared_bound_tendsto_zero {a b : ℕ → ℝ} (C : ℝ)
    (hstep : ∀ᶠ w in atTop, |a w| ^ 2 ≤ C * |b w|)
    (hb : Tendsto b atTop (𝓝 0)) : Tendsto a atTop (𝓝 0) := by
  have habs : Tendsto (fun w => |b w|) atTop (𝓝 0) := by
    simpa only [abs_zero] using hb.abs
  have hupper : Tendsto (fun w => C * |b w|) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul habs
  have hsq : Tendsto (fun w => |a w| ^ 2) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun _ => sq_nonneg _)) hstep hupper
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have haabs : Tendsto (fun w => |a w|) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_abs, Real.sqrt_zero] using hsqrt
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr haabs

theorem finite_squared_chain_tendsto_zero (n : ℕ) (A : ℕ → ℕ → ℝ)
    (C : ℕ → ℝ)
    (hstep : ∀ i < n, ∀ᶠ w in atTop, |A i w| ^ 2 ≤ C i * |A (i + 1) w|)
    (hterminal : Tendsto (A n) atTop (𝓝 0)) : Tendsto (A 0) atTop (𝓝 0) := by
  induction n generalizing A C with
  | zero => exact hterminal
  | succ n ih =>
    have htail := ih (fun i => A (i + 1)) (fun i => C (i + 1))
      (fun i hi => hstep (i + 1) (by omega)) hterminal
    exact squared_bound_tendsto_zero (C 0) (hstep 0 (Nat.zero_lt_succ n)) htail

end Hindman168
