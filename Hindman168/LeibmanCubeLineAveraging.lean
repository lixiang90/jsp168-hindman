import Hindman168.ComplexBoxTranslation
import Hindman168.FiniteComplexDenseMean

namespace Hindman168
open scoped BigOperators Classical

theorem leibman_cube_line_mean_error {κ : Type*} [Fintype κ]
    (N M L : ℕ) (hN : 0 < N) (hM : 0 < M) (q : κ → ℕ) (hq : ∀ j, q j ≤ L)
    (f : (κ → ℤ) → ℂ) (B : ℝ) (hB : 0 ≤ B) (hf : ∀ x, ‖f x‖ ≤ B) :
    ‖finiteComplexSetMean (Fintype.piFinset (fun _ : κ => Finset.Ico 0 (N : ℤ)))
        (fun x => finiteComplexSetMean (Finset.range M)
          (fun n => f (fun j => x j+(q j : ℤ)*(n : ℤ)))) -
      finiteComplexSetMean (Fintype.piFinset (fun _ : κ => Finset.Ico 0 (N : ℤ))) f‖ ≤
      2*B*(Fintype.card κ : ℝ)*(L : ℝ)*M/N := by
  let S := Fintype.piFinset (fun _ : κ => Finset.Ico 0 (N : ℤ))
  let a := fun n : ℕ => finiteComplexSetMean S (fun x => f (fun j => x j+(q j : ℤ)*(n : ℤ)))
  have hnr : (0 : ℝ) < N := by exact_mod_cast hN
  have hshift : ∀ n ∈ Finset.range M,
      ‖a n-finiteComplexSetMean S f‖ ≤ 2*B*(Fintype.card κ : ℝ)*(L : ℝ)*M/N := by
    intro n hn
    have htrans := complex_box_translation_bound (fun _ : κ => (0 : ℤ))
      (fun _ => (N : ℤ)) (fun j => (q j : ℤ)*(n : ℤ))
      (fun _ => by exact_mod_cast hN) f B hB hf
    simp only [Int.cast_zero, sub_zero, Int.cast_natCast, Int.cast_mul] at htrans
    apply htrans.trans
    have hsum : (∑ j : κ, 2*|(q j : ℝ)*(n : ℝ)| /
        (N : ℝ)) ≤ (Fintype.card κ : ℝ)*(2*(L : ℝ)*M/N) := by
      calc
        _ ≤ ∑ _j : κ, 2*(L : ℝ)*M/N := by
          apply Finset.sum_le_sum
          intro j _
          have hab : |(q j : ℝ)*(n : ℝ)| ≤ (L : ℝ)*M := by
            rw [abs_of_nonneg (by positivity)]
            exact_mod_cast Nat.mul_le_mul (hq j) (Finset.mem_range.mp hn).le
          exact div_le_div_of_nonneg_right
            (by nlinarith) hnr.le
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc
      _ ≤ B*((Fintype.card κ : ℝ)*(2*(L : ℝ)*M/N)) :=
        mul_le_mul_of_nonneg_left hsum hB
      _ = _ := by ring
  rw [finiteComplexSetMean_comm]
  exact finiteComplexSetMean_difference_norm_bound (Finset.range M)
    (Finset.nonempty_range_iff.mpr hM.ne') a (finiteComplexSetMean S f) _ (by positivity) hshift

theorem leibman_cube_line_dense_origins {κ : Type*} [Fintype κ]
    (N M L : ℕ) (hN : 0 < N) (hM : 0 < M) (q : κ → ℕ) (hq : ∀ j, q j ≤ L)
    (f : (κ → ℤ) → ℂ) (B δ : ℝ) (hB : 0 < B) (hδ : 0 ≤ δ)
    (hf : ∀ x, ‖f x‖ ≤ B)
    (herr : 2*B*(Fintype.card κ : ℝ)*(L : ℝ)*M/N ≤ δ*B/4)
    (hbad : δ*B ≤ ‖finiteComplexSetMean
      (Fintype.piFinset (fun _ : κ => Finset.Ico 0 (N : ℤ))) f‖) :
    δ/4*((Fintype.piFinset (fun _ : κ => Finset.Ico 0 (N : ℤ))).card : ℝ) ≤
      (((Fintype.piFinset (fun _ : κ => Finset.Ico 0 (N : ℤ))).filter (fun x =>
        δ*B/2 ≤ ‖finiteComplexSetMean (Finset.range M)
          (fun n => f (fun j => x j+(q j : ℤ)*(n : ℤ)))‖)).card : ℝ) := by
  let S := Fintype.piFinset (fun _ : κ => Finset.Ico 0 (N : ℤ))
  let a := fun x : κ → ℤ => finiteComplexSetMean (Finset.range M)
    (fun n => f (fun j => x j+(q j : ℤ)*(n : ℤ)))
  have hS : S.Nonempty := Fintype.piFinset_nonempty.mpr
    (fun _ => Finset.nonempty_Ico.mpr (by exact_mod_cast hN))
  have he := (leibman_cube_line_mean_error N M L hN hM q hq f B hB.le hf).trans herr
  have hnorm : 3*δ*B/4 ≤ ‖finiteComplexSetMean S a‖ := by
    have ht := norm_sub_norm_le (finiteComplexSetMean S f) (finiteComplexSetMean S a)
    rw [norm_sub_rev] at ht
    linarith
  exact finite_complex_mean_dense_large_values S hS a B δ hB hδ
    (fun x _ => finiteComplexSetMean_norm_bound (Finset.range M) _ B hB.le (fun _ _ => hf _)) hnorm

end Hindman168
