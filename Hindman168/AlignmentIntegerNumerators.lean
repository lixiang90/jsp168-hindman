import Hindman168.AlignmentIntegerPairScales
import Hindman168.SmoothAbsorption
import Mathlib.Data.Nat.Cast.Field

namespace Hindman168

theorem alignment_denominator_times_primorial_dvd {q₀ w : ℕ}
    (hq : 0 < q₀) (hw : q₀ + 1 ≤ w) : q₀ * primorial w ∣ (primorial w) ^ w := by
  have hd : q₀ ∣ (primorial w) ^ (w - 1) :=
    (fixed_integer_dvd_primorial_pow_self hq.ne' (by omega)).trans
      (pow_dvd_pow _ (by omega : q₀ ≤ w - 1))
  have he : w = (w - 1) + 1 := by omega
  have hp : (primorial w) ^ w = (primorial w) ^ (w - 1) * primorial w := by
    calc
      _ = (primorial w) ^ ((w - 1) + 1) := congrArg (fun z => (primorial w) ^ z) he
      _ = _ := pow_succ _ _
  rw [hp]
  exact Nat.mul_dvd_mul hd (dvd_refl _)

def alignmentIntegerNumerator {n : ℕ} {i : Fin n} (q₀ w : ℕ)
    (e : AlignmentAddingPair n i) (t : Fin n → ℕ) : ℕ :=
  (alignmentIntegerScale w (alignmentPairSourceBlock e) /
    (q₀ * alignmentIntegerScale w (alignmentPairTargetBlock e))) *
      alignmentNaturalBlockProduct t (alignmentPairSourceBlock e)

theorem alignmentPair_denominator_scale_factor {n : ℕ} {i : Fin n}
    {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀ + 1 ≤ w) (e : AlignmentAddingPair n i) :
    ∃ k : ℕ, alignmentIntegerScale w (alignmentPairSourceBlock e) =
      (q₀ * alignmentIntegerScale w (alignmentPairTargetBlock e)) *
        (primorial w * k) := by
  obtain ⟨c, hc⟩ := alignment_denominator_times_primorial_dvd hq hw
  obtain ⟨d, hd⟩ := alignmentPair_integer_scale_divisibility w e
  refine ⟨c * d, ?_⟩
  rw [hd, hc]
  ring

theorem alignmentIntegerNumerator_divisible {n : ℕ} {i : Fin n}
    {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀ + 1 ≤ w)
    (e : AlignmentAddingPair n i) (t : Fin n → ℕ) :
    primorial w ∣ alignmentIntegerNumerator q₀ w e t := by
  obtain ⟨k, hk⟩ := alignmentPair_denominator_scale_factor hq hw e
  unfold alignmentIntegerNumerator
  rw [hk, Nat.mul_div_cancel_left _
    (Nat.mul_pos hq (alignmentIntegerScale_positive w _))]
  exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _

theorem alignmentIntegerNumerator_rational_value {n : ℕ} {i : Fin n}
    {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀ + 1 ≤ w)
    (e : AlignmentAddingPair n i) (t : Fin n → ℕ) :
    (alignmentIntegerNumerator q₀ w e t : ℚ) =
      (alignmentIntegerScale w (alignmentPairSourceBlock e) : ℚ) /
        ((q₀ : ℚ) * alignmentIntegerScale w (alignmentPairTargetBlock e)) *
          alignmentNaturalBlockProduct t (alignmentPairSourceBlock e) := by
  obtain ⟨k, hk⟩ := alignmentPair_denominator_scale_factor hq hw e
  have hd : q₀ * alignmentIntegerScale w (alignmentPairTargetBlock e) ∣
      alignmentIntegerScale w (alignmentPairSourceBlock e) := ⟨primorial w * k, hk⟩
  simp only [alignmentIntegerNumerator, Nat.cast_mul, Nat.cast_div_charZero hd]

end Hindman168
