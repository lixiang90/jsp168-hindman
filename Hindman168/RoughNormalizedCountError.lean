import Hindman168.RoughCoprimeResidueIntersection
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace Hindman168

theorem rough_normalized_count_error (n c b K : ℝ) (hb : 2 ≤ b) (hK : 1 ≤ K)
    (hn : |n - b / K| ≤ 1) (hc : |c - b| ≤ 1) :
    0 < c ∧ |n / c - 1 / K| ≤ 4 / b := by
  have hbpos : 0 < b := by linarith
  have hKpos : 0 < K := by linarith
  have hclow := (abs_le.mp hc).1
  have hcpos : 0 < c := by linarith
  have hcb : b / 2 ≤ c := by linarith
  have hrec : 1 / K ≤ (1 : ℝ) := (div_le_one hKpos).mpr hK
  have hnum : |n - c / K| ≤ 2 := by
    have he : n - c / K = (n - b / K) + (b - c) / K := by ring
    rw [he]
    calc
      _ ≤ |n - b / K| + |(b - c) / K| := abs_add_le _ _
      _ ≤ 1 + 1 / K := by
        rw [abs_div, abs_of_pos hKpos, abs_sub_comm b c]
        exact add_le_add hn (div_le_div_of_nonneg_right hc hKpos.le)
      _ ≤ 2 := by linarith
  refine ⟨hcpos, ?_⟩
  have he : n / c - 1 / K = (n - c / K) / c := by field_simp
  rw [he, abs_div, abs_of_pos hcpos]
  calc
    _ ≤ 2 / c := div_le_div_of_nonneg_right hnum hcpos.le
    _ ≤ 4 / b := by
      apply (div_le_div_iff₀ hcpos hbpos).mpr
      linarith

theorem rough_coprime_interval_residue_weight (A B a u : ℤ) (t K : ℕ)
    (ht : 0 < t) (hK : 0 < K) (hcop : t.Coprime K)
    (hlen : 2 * (t : ℝ) ≤ (B : ℝ) - A) :
    0 < (alignmentIntervalClass A B t a).card ∧
      |((alignmentIntervalClass A B t a ∩ alignmentIntervalClass A B K u).card : ℝ) /
        (alignmentIntervalClass A B t a).card - 1 / (K : ℝ)| ≤
        4 * (t : ℝ) / ((B : ℝ) - A) := by
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have hAB : A ≤ B := by
    have : (A : ℝ) ≤ B := by linarith
    exact_mod_cast this
  have hb : 2 ≤ ((B : ℝ) - A) / t := (le_div_iff₀ htpos).mpr hlen
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hn := rough_coprime_interval_intersection_count A B a u t K ht hK hcop hAB
  have hc := alignment_interval_class_count A B a t ht hAB
  rw [Nat.cast_mul, div_mul_eq_div_div] at hn
  obtain ⟨hpos, hweight⟩ := rough_normalized_count_error _ _ _ _ hb hKr hn hc
  refine ⟨by exact_mod_cast hpos, ?_⟩
  have he : 4 / (((B : ℝ) - A) / t) = 4 * (t : ℝ) / ((B : ℝ) - A) := by
    rw [div_div_eq_mul_div]
  rw [he] at hweight
  exact hweight

end Hindman168
