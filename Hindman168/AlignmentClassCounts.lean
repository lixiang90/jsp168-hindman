import Hindman168.AlignmentIntervalMeans
import Hindman168.IntervalResidueCount

namespace Hindman168
open scoped Classical

theorem alignment_interval_class_count (A B r : ℤ) (d : ℕ) (hd : 0 < d) (hAB : A ≤ B) :
    |((alignmentIntervalClass A B d r).card : ℝ) - ((B : ℝ) - A) / d| ≤ 1 := by
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
  have hr0 := Int.emod_nonneg r hdZ.ne'
  have hrlt := Int.emod_lt_of_pos r hdZ
  have hr : (r % (d : ℤ)).toNat < d := by
    have hh : ((r % (d : ℤ)).toNat : ℤ) < d := by rw [Int.toNat_of_nonneg hr0]; exact hrlt
    exact_mod_cast hh
  have hlen : ((B - A).toNat : ℤ) = B - A := Int.toNat_of_nonneg (sub_nonneg.mpr hAB)
  have he : alignmentIntervalClass A B d r =
      intervalResidueSet A (B - A).toNat d (r % (d : ℤ)).toNat := by
    ext z
    simp only [alignmentIntervalClass, intervalResidueSet, integerWindow,
      hlen, add_sub_cancel, Finset.mem_filter, Int.ModEq, Int.toNat_of_nonneg hr0]
    exact and_congr_right (fun _ => eq_comm)
  rw [he]
  have h := interval_residue_count A (B - A).toNat hd hr
  have hlenR : ((B - A).toNat : ℝ) = (B : ℝ) - A := by exact_mod_cast hlen
  simpa only [hlenR] using h

theorem alignment_interval_class_nonempty (A B r : ℤ) (d : ℕ) (hd : 0 < d)
    (hAB : 2 * (d : ℤ) ≤ B - A) : (alignmentIntervalClass A B d r).Nonempty := by
  have h := alignment_interval_class_count A B r d hd (by omega)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hl : 2 * (d : ℝ) ≤ (B : ℝ) - A := by exact_mod_cast hAB
  have hdiv : (2 : ℝ) ≤ ((B : ℝ) - A) / d := (le_div_iff₀ hdR).mpr hl
  have hc := (abs_le.mp h).1
  apply Finset.card_pos.mp
  have : (0 : ℝ) < (alignmentIntervalClass A B d r).card := by linarith
  exact_mod_cast this

end Hindman168
