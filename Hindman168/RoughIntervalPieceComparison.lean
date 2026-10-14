import Hindman168.RoughNormalizedPieceWeights

namespace Hindman168

theorem rough_interval_piece_weight_difference (A B l r a u : ℤ) (t K : ℕ)
    (ht : 0 < t) (hK : 0 < K) (hcop : t.Coprime K)
    (hAl : A ≤ l) (hlr : l ≤ r) (hrB : r ≤ B)
    (hlen : 2 * (t : ℝ) ≤ (B : ℝ) - A) :
    |((alignmentIntervalClass l r t a ∩ alignmentIntervalClass l r K u).card : ℝ) /
        (alignmentIntervalClass A B t a).card -
      ((alignmentIntervalClass l r K u).card : ℝ) / (Finset.Ico A B).card| ≤
        5 * (t : ℝ) / ((B : ℝ) - A) := by
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hLpos : 0 < (B : ℝ) - A := by linarith
  have hAB : A ≤ B := hAl.trans (hlr.trans hrB)
  have hcard : ((Finset.Ico A B).card : ℝ) = (B : ℝ) - A := by
    have he : ((B - A).toNat : ℤ) = B - A := Int.toNat_of_nonneg (sub_nonneg.mpr hAB)
    simp only [Int.card_Ico]
    exact_mod_cast he
  rw [hcard]
  have hp := (rough_interval_piece_residue_weight A B l r a u t K ht hK hcop
    hAl hlr hrB hlen).2
  have hq : |((alignmentIntervalClass l r K u).card : ℝ) / ((B : ℝ) - A) -
      ((r : ℝ) - l) / (((B : ℝ) - A) * K)| ≤ 1 / ((B : ℝ) - A) := by
    have he : ((alignmentIntervalClass l r K u).card : ℝ) / ((B : ℝ) - A) -
        ((r : ℝ) - l) / (((B : ℝ) - A) * K) =
      (((alignmentIntervalClass l r K u).card : ℝ) - ((r : ℝ) - l) / K) /
        ((B : ℝ) - A) := by field_simp
    rw [he, abs_div, abs_of_pos hLpos]
    exact div_le_div_of_nonneg_right (alignment_interval_class_count l r u K hK hlr) hLpos.le
  calc
    _ ≤ |((alignmentIntervalClass l r t a ∩ alignmentIntervalClass l r K u).card : ℝ) /
        (alignmentIntervalClass A B t a).card - ((r : ℝ) - l) / (((B : ℝ) - A) * K)| +
      |((r : ℝ) - l) / (((B : ℝ) - A) * K) -
        ((alignmentIntervalClass l r K u).card : ℝ) / ((B : ℝ) - A)| := abs_sub_le _ _ _
    _ ≤ 5 * (t : ℝ) / ((B : ℝ) - A) := by
      rw [abs_sub_comm] at hq
      have he := add_le_add hp hq
      apply he.trans
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ hLpos.le
      linarith

end Hindman168
