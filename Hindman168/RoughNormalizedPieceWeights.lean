import Hindman168.RoughNormalizedCountError

namespace Hindman168

theorem rough_normalized_piece_count_error (n c b p : ℝ) (hb : 2 ≤ b)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hn : |n - b * p| ≤ 1) (hc : |c - b| ≤ 1) :
    0 < c ∧ |n / c - p| ≤ 4 / b := by
  have hbpos : 0 < b := by linarith
  have hclow := (abs_le.mp hc).1
  have hcpos : 0 < c := by linarith
  have hcb : b / 2 ≤ c := by linarith
  have hnum : |n - c * p| ≤ 2 := by
    have he : n - c * p = (n - b * p) + (b - c) * p := by ring
    rw [he]
    calc
      _ ≤ |n - b * p| + |(b - c) * p| := abs_add_le _ _
      _ ≤ 1 + p := by
        rw [abs_mul, abs_of_nonneg hp0, abs_sub_comm b c]
        exact add_le_add hn (by simpa using mul_le_mul_of_nonneg_right hc hp0)
      _ ≤ 2 := by linarith
  refine ⟨hcpos, ?_⟩
  have he : n / c - p = (n - c * p) / c := by field_simp
  rw [he, abs_div, abs_of_pos hcpos]
  calc
    _ ≤ 2 / c := div_le_div_of_nonneg_right hnum hcpos.le
    _ ≤ 4 / b := by
      apply (div_le_div_iff₀ hcpos hbpos).mpr
      linarith

theorem rough_interval_piece_residue_weight (A B l r a u : ℤ) (t K : ℕ)
    (ht : 0 < t) (hK : 0 < K) (hcop : t.Coprime K)
    (hAl : A ≤ l) (hlr : l ≤ r) (hrB : r ≤ B)
    (hlen : 2 * (t : ℝ) ≤ (B : ℝ) - A) :
    0 < (alignmentIntervalClass A B t a).card ∧
      |((alignmentIntervalClass l r t a ∩ alignmentIntervalClass l r K u).card : ℝ) /
        (alignmentIntervalClass A B t a).card -
          ((r : ℝ) - l) / (((B : ℝ) - A) * K)| ≤
        4 * (t : ℝ) / ((B : ℝ) - A) := by
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hLpos : 0 < (B : ℝ) - A := by linarith
  have hl0 : 0 ≤ (r : ℝ) - l := by exact_mod_cast sub_nonneg.mpr hlr
  have hlL : (r : ℝ) - l ≤ (B : ℝ) - A := by
    have h1 : (A : ℝ) ≤ l := by exact_mod_cast hAl
    have h2 : (r : ℝ) ≤ B := by exact_mod_cast hrB
    linarith
  have hp0 : 0 ≤ ((r : ℝ) - l) / (((B : ℝ) - A) * K) := by positivity
  have hp1 : ((r : ℝ) - l) / (((B : ℝ) - A) * K) ≤ 1 := by
    apply (div_le_one (mul_pos hLpos hKpos)).mpr
    have hmult : (B : ℝ) - A ≤ ((B : ℝ) - A) * K := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hKr hLpos.le
    exact hlL.trans hmult
  have hb : 2 ≤ ((B : ℝ) - A) / t := (le_div_iff₀ htpos).mpr hlen
  have hn := rough_coprime_interval_intersection_count l r a u t K ht hK hcop hlr
  have hc := alignment_interval_class_count A B a t ht (hAl.trans (hlr.trans hrB))
  have he : (((B : ℝ) - A) / t) *
      (((r : ℝ) - l) / (((B : ℝ) - A) * K)) = ((r : ℝ) - l) / (t * K : ℕ) := by
    rw [Nat.cast_mul]
    field_simp
  rw [← he] at hn
  obtain ⟨hpos, hw⟩ := rough_normalized_piece_count_error _ _ _ _ hb hp0 hp1 hn hc
  refine ⟨by exact_mod_cast hpos, ?_⟩
  simpa only [div_div_eq_mul_div] using hw

end Hindman168
