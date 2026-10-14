import Hindman168.CutoffGrowth
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.GCD.Basic

/-!
# Explicit growing gap lengths divisible by every finite requirement

The finite requirements exclude zero polynomial values. Multiplying their
LCM by a growing integer preserves all divisibilities and supplies the
paper's w*B^w lower bound. No upper size bound is needed.
-/

namespace Hindman168

open Filter
open scoped Topology

def gapMultiple (S : Finset ℕ) (B w : ℕ) : ℕ := S.lcm id * ((w + 1) * (B + 1) ^ w)

theorem gapMultiple_lcm_pos {S : Finset ℕ} (hS : ∀ n ∈ S, 0 < n) : 0 < S.lcm id := by
  exact Nat.pos_of_ne_zero ((Finset.lcm_ne_zero_iff).mpr (fun n hn => (hS n hn).ne'))

theorem gapMultiple_pos {S : Finset ℕ} (hS : ∀ n ∈ S, 0 < n) (B w : ℕ) :
    0 < gapMultiple S B w :=
  Nat.mul_pos (gapMultiple_lcm_pos hS) (Nat.mul_pos (by omega) (Nat.pow_pos (by omega)))

theorem gapMultiple_dvd {S : Finset ℕ} {n : ℕ} (hn : n ∈ S) (B w : ℕ) :
    n ∣ gapMultiple S B w :=
  (Finset.dvd_lcm hn).trans (dvd_mul_right _ _)

theorem gapMultiple_lower {S : Finset ℕ} (hS : ∀ n ∈ S, 0 < n) (B w : ℕ) :
    w * B ^ w ≤ gapMultiple S B w := by
  have hfirst : w * B ^ w ≤ (w + 1) * (B + 1) ^ w :=
    Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega : B ≤ B + 1) w)
  have hL : 1 ≤ S.lcm id := gapMultiple_lcm_pos hS
  apply hfirst.trans
  change (w + 1) * (B + 1) ^ w ≤ S.lcm id * ((w + 1) * (B + 1) ^ w)
  simpa only [one_mul] using Nat.mul_le_mul_right ((w + 1) * (B + 1) ^ w) hL

theorem gapMultiple_powerDominates {S : ℕ → Finset ℕ} {B : ℕ → ℕ}
    (hS : ∀ w n, n ∈ S w → 0 < n) (hB : ∀ᶠ w in atTop, 1 ≤ B w) :
    PowerDominates atTop (fun w => (gapMultiple (S w) (B w) w : ℝ)) (fun w => (B w : ℝ)) := by
  apply powerDominates_of_parameter_power (hB.mono (fun _ hw => by exact_mod_cast hw))
  exact Eventually.of_forall (fun w => by exact_mod_cast gapMultiple_lower (hS w) (B w) w)

theorem gapMultiple_dyadic_log_powerDominates {S : ℕ → Finset ℕ} {B : ℕ → ℕ}
    (hS : ∀ w n, n ∈ S w → 0 < n) :
    PowerDominates atTop (fun w => Real.log (dyadicHarmonicCutoff (gapMultiple (S w) (B w) w) w))
      (fun w => (gapMultiple (S w) (B w) w : ℝ)) :=
  dyadicHarmonicCutoff_powerDominates (Eventually.of_forall (fun w =>
    gapMultiple_pos (hS w) (B w) w))

end Hindman168
