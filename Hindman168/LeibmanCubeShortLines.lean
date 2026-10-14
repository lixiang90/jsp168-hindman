import Hindman168.LeibmanCubeLineAveraging

namespace Hindman168
open scoped BigOperators Classical

theorem leibman_equal_cube_dense_short_lines {κ : Type*} [Fintype κ]
    (N L : ℕ) (hL : 0 < L) (hN : L^2 ≤ N)
    (q : κ → ℕ) (hq : ∀ j, q j ≤ L)
    (f : (κ → ℤ) → ℂ) (B δ : ℝ) (hB : 0 < B) (hδ : 0 ≤ δ)
    (hsize : 8*(Fintype.card κ : ℝ) ≤ δ*L)
    (hf : ∀ x, ‖f x‖ ≤ B)
    (hbad : δ*B ≤ ‖finiteComplexSetMean
      (Fintype.piFinset (fun _ : κ => Finset.Ico 0 (N : ℤ))) f‖) :
    δ/4*((Fintype.piFinset (fun _ : κ => Finset.Ico 0 (N : ℤ))).card : ℝ) ≤
      (((Fintype.piFinset (fun _ : κ => Finset.Ico 0 (N : ℤ))).filter (fun x =>
        δ*B/2 ≤ ‖finiteComplexSetMean (Finset.range (N/L^2))
          (fun n => f (fun j => x j+(q j : ℤ)*(n : ℤ)))‖)).card : ℝ) := by
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity) hN
  have hM : 0 < N/L^2 := Nat.div_pos hN (by positivity)
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hprod : ((N/L^2 : ℕ) : ℝ)*(L : ℝ)^2 ≤ N := by
    exact_mod_cast Nat.div_mul_le_self N (L^2)
  have hratio : (L : ℝ)*(N/L^2 : ℕ)/N ≤ (1 : ℝ)/L := by
    apply (le_div_iff₀ hLr).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hNr).mpr
    nlinarith [hprod]
  have herr : 2*B*(Fintype.card κ : ℝ)*(L : ℝ)*(N/L^2 : ℕ)/N ≤ δ*B/4 := by
    calc
      _ = (2*B*(Fintype.card κ : ℝ))*((L : ℝ)*(N/L^2 : ℕ)/N) := by ring
      _ ≤ (2*B*(Fintype.card κ : ℝ))*(1/L) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ ≤ δ*B/4 := by
        rw [← mul_div_assoc, mul_one]
        apply (div_le_iff₀ hLr).mpr
        have hb := mul_le_mul_of_nonneg_right hsize hB.le
        nlinarith
  exact leibman_cube_line_dense_origins N (N/L^2) L hNpos hM q hq f B δ hB hδ hf herr hbad

end Hindman168
