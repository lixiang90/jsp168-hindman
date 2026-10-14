import Hindman168.AlignmentShortPosteriorBound
import Hindman168.NormalizedShortBinCutoff

namespace Hindman168
open scoped BigOperators Classical

theorem binaryDyadicProduct_bounds {n : ℕ} (T : Finset (Fin n)) (x : Fin n → ℕ)
    (hx : ∀ j ∈ T, 0 < x j) :
    (∏ j ∈ T, 2 ^ Nat.log2 (x j)) ≤ alignmentNaturalBlockProduct x T ∧
      alignmentNaturalBlockProduct x T ≤ 2 ^ T.card * ∏ j ∈ T, 2 ^ Nat.log2 (x j) := by
  constructor
  · exact Finset.prod_le_prod' (fun j hj => Nat.log2_self_le (hx j hj).ne')
  · calc
      alignmentNaturalBlockProduct x T ≤ ∏ j ∈ T, 2 * 2 ^ Nat.log2 (x j) :=
        Finset.prod_le_prod' (fun j _ => by
          have hh := (Nat.lt_log2_self (n := x j)).le
          simpa only [pow_succ, mul_comm] using hh)
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const]

def alignmentShortCutoffGood {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (T : Finset (Fin n)) (x : Fin n → ℕ) : Prop :=
  F.cutoff w i.val * (2 ^ T.card * ∏ j ∈ T, 2 ^ Nat.log2 (x j)) ≤ alignmentShortBinStart F w i T x ∧
  alignmentShortBinStart F w i T x + alignmentShortBinVolume F w i T x ≤
    F.cutoff w i.val ^ 2 * ∏ j ∈ T, 2 ^ Nat.log2 (x j)

theorem alignment_short_cutoff_failure_normalized {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (T : Finset (Fin n)) (x : Fin n → ℕ)
    (hx : ∀ j ∈ T, 0 < x j)
    (hR : 0 < alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w))
    (hbad : ¬ alignmentShortCutoffGood F w i T x) :
    failedCutoffShortBin (F.cutoff w i.val)
      (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) 1 (2 ^ T.card) (x i) := by
  have hv : 0 < alignmentShortBinVolume F w i T x := by
    unfold alignmentShortBinVolume
    positivity
  have hb := (sameNaturalShortBin_iff hv
    (alignmentNaturalBlockProduct x T * x i) (alignmentNaturalBlockProduct x T * x i)).mp rfl
  have hd := binaryDyadicProduct_bounds T x hx
  apply shortBin_bad_endpoints_failed_normalized (x i)
    (tlo := (∏ j ∈ T, 2 ^ Nat.log2 (x j) : ℕ))
    (t := (alignmentNaturalBlockProduct x T : ℕ))
    (Q := (alignmentShortBinStart F w i T x : ℕ))
    (by positivity) (by exact_mod_cast (Nat.one_le_pow T.card 2 (by decide)))
    (Nat.cast_nonneg _) (by exact_mod_cast hd.1) (by exact_mod_cast hd.2)
    (by exact_mod_cast hb.1)
    (by simpa only [alignmentShortBinVolume, Nat.cast_add, Nat.cast_mul] using
      (show ((alignmentNaturalBlockProduct x T * x i : ℕ) : ℝ) <
        (alignmentShortBinStart F w i T x : ℝ) + alignmentShortBinVolume F w i T x from by exact_mod_cast hb.2))
  unfold alignmentShortCutoffGood at hbad
  rw [not_and_or, not_le, not_le] at hbad
  rcases hbad with h | h
  · left
    exact_mod_cast h
  · right
    simpa only [alignmentShortBinVolume, Nat.cast_add, Nat.cast_mul, Nat.cast_pow] using
      (show ((F.cutoff w i.val ^ 2 * ∏ j ∈ T, 2 ^ Nat.log2 (x j) : ℕ) : ℝ) <
        (alignmentShortBinStart F w i T x : ℝ) + alignmentShortBinVolume F w i T x from by exact_mod_cast h)

end Hindman168
