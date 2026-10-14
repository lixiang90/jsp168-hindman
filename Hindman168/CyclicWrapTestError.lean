import Hindman168.CyclicCellInterior

namespace Hindman168
open scoped BigOperators

theorem cyclic_interior_test_error (q H : ℕ) [NeZero q] (f g : ZMod q → ℝ)
    (hf : ∀ z, |f z| ≤ 1) (hg : ∀ z, |g z| ≤ 1)
    (he : ∀ z, H ≤ z.val → z.val + H < q → f z = g z) :
    |finiteHaarMean f - finiteHaarMean g| ≤ 4 * (H : ℝ) / q := by
  classical
  let B := (Finset.univ : Finset (ZMod q)).filter (fun z => ¬ (H ≤ z.val ∧ z.val + H < q))
  have hs : |∑ z : ZMod q, (f z - g z)| ≤ (B.card : ℝ) * 2 := by
    calc
      _ ≤ ∑ z : ZMod q, |f z - g z| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ z : ZMod q, if ¬ (H ≤ z.val ∧ z.val + H < q) then (2 : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro z _
        by_cases hi : H ≤ z.val ∧ z.val + H < q
        · simp [hi, he z hi.1 hi.2]
        · simp only [hi, not_false_eq_true, if_true]
          calc
            _ ≤ |f z| + |g z| := by simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (f z) (-g z)
            _ ≤ 2 := by linarith [hf z, hg z]
      _ = _ := by rw [← Finset.sum_filter]; simp [B]
  have hc : (B.card : ℝ) ≤ 2 * H := by exact_mod_cast cyclic_boundary_card q H
  unfold finiteHaarMean
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (Fintype.card (ZMod q) : ℝ) from Nat.cast_nonneg _), ZMod.card]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg q)
  nlinarith

theorem cyclicCell_product_wrap_error {ι : Type*} (S : Finset ι)
    (k : ℤ) (M q H : ℕ) [NeZero q] (r : Fin M)
    (h : ι → ℤ) (hh : ∀ i ∈ S, |h i| ≤ (H : ℤ))
    (f : ℤ → ℝ) (hf : ∀ y, |f y| ≤ 1) :
    |finiteHaarMean (fun z : ZMod q =>
        ∏ i ∈ S, f (k * (M * q : ℕ) + r.val + (M : ℤ) * (z + (h i : ZMod q)).val)) -
      finiteHaarMean (fun z : ZMod q =>
        ∏ i ∈ S, f (k * (M * q : ℕ) + r.val + (M : ℤ) * z.val + M * h i))| ≤
      4 * (H : ℝ) / q := by
  apply cyclic_interior_test_error q H
  · intro z
    rw [Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun _ _ => hf _)
  · intro z
    rw [Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun _ _ => hf _)
  · intro z hl hu
    exact cyclicCell_product_eq_of_interior S k M q H r z h hh hl hu f

end Hindman168
