import Mathlib.Data.Nat.Squarefree
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# An explicit logarithmic lower bound for squarefree harmonic sums

Every positive integer is a square times a squarefree integer. Covering
the finite interval by these products, then summing reciprocals, bounds
the full harmonic sum by twice the squarefree harmonic sum. The finite
square reciprocal sum is bounded by 2 using mathlib's telescoping bound.
-/

namespace Hindman168

open scoped BigOperators Classical

def squarefreeWindow (z : ℕ) : Finset ℕ := (Finset.Icc 1 z).filter Squarefree

noncomputable def squarefreeHarmonic (z : ℕ) : ℝ :=
  ∑ d ∈ squarefreeWindow z, (d : ℝ)⁻¹

theorem squarefreeHarmonic_nonneg (z : ℕ) : 0 ≤ squarefreeHarmonic z :=
  Finset.sum_nonneg (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))

theorem square_reciprocal_sum_le_two (z : ℕ) :
    (∑ k ∈ Finset.Icc 1 z, ((k : ℝ) ^ 2)⁻¹) ≤ 2 := by
  by_cases hz : z = 0
  · simp [hz]
  have hz1 : 1 ≤ z := by omega
  have he : Finset.Icc 1 z = insert 1 (Finset.Ioc 1 z) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
    omega
  rw [he, Finset.sum_insert (by simp)]
  have hs := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := 1) (n := z) (by decide) hz1
  norm_num at hs ⊢
  linarith [inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) z)]

theorem positive_interval_squarefree_product_cover (z : ℕ) :
    Finset.Icc 1 z ⊆ ((Finset.Icc 1 z) ×ˢ squarefreeWindow z).image
      (fun kd : ℕ × ℕ => kd.1 ^ 2 * kd.2) := by
  intro n hn
  obtain ⟨hn1, hnz⟩ := Finset.mem_Icc.mp hn
  obtain ⟨d, k, hd, hk, he, hsf⟩ := Nat.sq_mul_squarefree_of_pos (by omega : 0 < n)
  have hk2 : 1 ≤ k ^ 2 := one_le_pow₀ (by omega : 1 ≤ k)
  have hdle : d ≤ n := by
    calc
      d = 1 * d := by omega
      _ ≤ k ^ 2 * d := Nat.mul_le_mul_right d hk2
      _ = n := he
  have hk2le : k ^ 2 ≤ n := by
    calc
      k ^ 2 = k ^ 2 * 1 := by omega
      _ ≤ k ^ 2 * d := Nat.mul_le_mul_left _ (by omega : 1 ≤ d)
      _ = n := he
  have hkle : k ≤ k ^ 2 := by nlinarith
  apply Finset.mem_image.mpr
  exact ⟨(k, d), Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨hk, (hkle.trans hk2le).trans hnz⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hd, hdle.trans hnz⟩, hsf⟩⟩, he⟩

theorem harmonic_le_twice_squarefreeHarmonic (z : ℕ) :
    (harmonic z : ℝ) ≤ 2 * squarefreeHarmonic z := by
  let S := (Finset.Icc 1 z) ×ˢ squarefreeWindow z
  let f : ℕ × ℕ → ℕ := fun kd => kd.1 ^ 2 * kd.2
  have hcover : Finset.Icc 1 z ⊆ S.image f := positive_interval_squarefree_product_cover z
  calc
    _ = ∑ n ∈ Finset.Icc 1 z, (n : ℝ)⁻¹ := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ ∑ n ∈ S.image f, (n : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hcover (fun n _ _ => by positivity)
    _ ≤ ∑ kd ∈ S, ((f kd : ℕ) : ℝ)⁻¹ :=
      Finset.sum_image_le_of_nonneg (fun n _ => by positivity)
    _ = (∑ k ∈ Finset.Icc 1 z, ((k : ℝ) ^ 2)⁻¹) * squarefreeHarmonic z := by
      simp only [S, f, Finset.sum_product, Nat.cast_mul, Nat.cast_pow, mul_inv,
        squarefreeHarmonic, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_right (square_reciprocal_sum_le_two z)
      (squarefreeHarmonic_nonneg z)

theorem squarefreeHarmonic_log_lower (z : ℕ) :
    Real.log (z + 1 : ℕ) / 2 ≤ squarefreeHarmonic z := by
  have h := (log_add_one_le_harmonic z).trans (harmonic_le_twice_squarefreeHarmonic z)
  linarith

end Hindman168
