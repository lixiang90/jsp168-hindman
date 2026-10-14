import Hindman168.CyclicWrapTestError

namespace Hindman168
open scoped BigOperators

theorem shortCube_vertex_shift_bound (d L a : ℕ) (u v : Fin d → Fin L) (ω : Finset (Fin d)) :
    |(a : ℤ) * ∑ j ∈ ω, (((v j).val : ℤ) - (u j).val)| ≤ (d * a * L : ℕ) := by
  have hb (j : Fin d) : |((v j).val : ℤ) - (u j).val| ≤ (L : ℤ) := by
    rw [abs_le]
    have hu := (u j).isLt
    have hv := (v j).isLt
    omega
  have hc : ω.card ≤ d := by simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_card (Finset.subset_univ ω)
  have hs : |∑ j ∈ ω, (((v j).val : ℤ) - (u j).val)| ≤ (d : ℤ) * L := by
    calc
      _ ≤ ∑ j ∈ ω, |((v j).val : ℤ) - (u j).val| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ ω, (L : ℤ) := Finset.sum_le_sum (fun j _ => hb j)
      _ = (ω.card : ℤ) * L := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (Int.natCast_nonneg L)
  rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg a)]
  have he := mul_le_mul_of_nonneg_left hs (Int.natCast_nonneg a)
  calc
    _ ≤ (a : ℤ) * ((d : ℤ) * L) := he
    _ = _ := by push_cast; ring

theorem shortCube_wrap_margin_ratio (q d J a : ℕ) (hq : 0 < q) (hJ : 0 < J) :
    4 * (d * a * (q / (J * a)) : ℕ) / (q : ℝ) ≤ 4 * (d : ℝ) / J := by
  have hn := Nat.mul_div_le q (J * a)
  have he : J * (d * a * (q / (J * a))) ≤ d * q := by nlinarith [Nat.mul_le_mul_left d hn]
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hjr : (0 : ℝ) < J := by exact_mod_cast hJ
  apply (div_le_div_iff₀ hqr hjr).mpr
  have her : (J : ℝ) * (d * a * (q / (J * a)) : ℕ) ≤ (d : ℝ) * q := by exact_mod_cast he
  nlinarith

theorem cyclicCell_shortCube_wrap_error (k : ℤ) (M q d J a : ℕ) [NeZero q]
    (hJ : 0 < J) (r : Fin M) (u v : Fin d → Fin (q / (J * a)))
    (f : ℤ → ℝ) (hf : ∀ y, |f y| ≤ 1) :
    |finiteHaarMean (fun z : ZMod q =>
        ∏ ω : Finset (Fin d), f (k * (M * q : ℕ) + r.val + (M : ℤ) *
          (z + (((a : ℤ) * ∑ j ∈ ω, (((v j).val : ℤ) - (u j).val) : ℤ) : ZMod q)).val)) -
      finiteHaarMean (fun z : ZMod q =>
        ∏ ω : Finset (Fin d), f (k * (M * q : ℕ) + r.val + (M : ℤ) * z.val +
          M * ((a : ℤ) * ∑ j ∈ ω, (((v j).val : ℤ) - (u j).val))))| ≤
      4 * (d : ℝ) / J := by
  exact (cyclicCell_product_wrap_error Finset.univ k M q (d * a * (q / (J * a))) r
    (fun ω => (a : ℤ) * ∑ j ∈ ω, (((v j).val : ℤ) - (u j).val))
    (fun ω _ => shortCube_vertex_shift_bound d (q / (J * a)) a u v ω) f hf).trans
    (shortCube_wrap_margin_ratio q d J a (Nat.pos_of_ne_zero (NeZero.ne q)) hJ)

end Hindman168
