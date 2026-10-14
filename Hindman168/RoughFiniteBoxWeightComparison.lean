import Hindman168.RoughBoxPieceWeights

namespace Hindman168
open scoped BigOperators Classical

theorem rough_finite_box_piece_weights {ι β : Type*} [Fintype ι]
    (pieces : Finset β) (A B a : ι → ℤ) (l r u : β → ι → ℤ) (t K : ℕ)
    (ht : 0 < t) (hK : 0 < K) (hcop : t.Coprime K)
    (hAl : ∀ i ∈ pieces, ∀ j, A j ≤ l i j) (hlr : ∀ i ∈ pieces, ∀ j, l i j ≤ r i j)
    (hrB : ∀ i ∈ pieces, ∀ j, r i j ≤ B j)
    (hlen : ∀ j, 2 * (t : ℝ) ≤ (B j : ℝ) - A j) :
    (∑ i ∈ pieces,
      |((alignmentBoxClass (l i) (r i) a t ∩ alignmentBoxClass (l i) (r i) (u i) K).card : ℝ) /
          (alignmentBoxClass A B a t).card -
        ((alignmentBoxClass (l i) (r i) (u i) K).card : ℝ) /
          (Fintype.piFinset (fun j => Finset.Ico (A j) (B j))).card|) ≤
      (pieces.card : ℝ) * ∑ j, 5 * (t : ℝ) / ((B j : ℝ) - A j) := by
  calc
    _ ≤ ∑ _i ∈ pieces, ∑ j, 5 * (t : ℝ) / ((B j : ℝ) - A j) := by
      apply Finset.sum_le_sum
      intro i hi
      exact rough_box_piece_weight_difference A B (l i) (r i) a (u i) t K ht hK hcop
        (hAl i hi) (hlr i hi) (hrB i hi) hlen
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

theorem rough_finite_box_piece_weights_scaled {ι β : Type*} [Fintype ι]
    (pieces : Finset β) (A B a : ι → ℤ) (l r u : β → ι → ℤ) (t K : ℕ)
    (ht : 0 < t) (hK : 0 < K) (hcop : t.Coprime K)
    (hAl : ∀ i ∈ pieces, ∀ j, A j ≤ l i j) (hlr : ∀ i ∈ pieces, ∀ j, l i j ≤ r i j)
    (hrB : ∀ i ∈ pieces, ∀ j, r i j ≤ B j)
    (c Z : ℝ) (hc : 0 < c) (hZ : 0 < Z) (htZ : 2 * (t : ℝ) ≤ c * Z)
    (hlen : ∀ j, c * Z ≤ (B j : ℝ) - A j) :
    (∑ i ∈ pieces,
      |((alignmentBoxClass (l i) (r i) a t ∩ alignmentBoxClass (l i) (r i) (u i) K).card : ℝ) /
          (alignmentBoxClass A B a t).card -
        ((alignmentBoxClass (l i) (r i) (u i) K).card : ℝ) /
          (Fintype.piFinset (fun j => Finset.Ico (A j) (B j))).card|) ≤
      (pieces.card : ℝ) * Fintype.card ι * (5 * (t : ℝ) / (c * Z)) := by
  apply (rough_finite_box_piece_weights pieces A B a l r u t K ht hK hcop hAl hlr hrB
    (fun j => htZ.trans (hlen j))).trans
  have hs : (∑ j, 5 * (t : ℝ) / ((B j : ℝ) - A j)) ≤
      (Fintype.card ι : ℝ) * (5 * (t : ℝ) / (c * Z)) := by
    calc
      _ ≤ ∑ _j : ι, 5 * (t : ℝ) / (c * Z) := by
        apply Finset.sum_le_sum
        intro j _
        exact div_le_div_of_nonneg_left (by positivity) (mul_pos hc hZ) (hlen j)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg pieces.card)

end Hindman168
