import Hindman168.RoughBoxPartition
import Hindman168.RoughResiduePieceNonempty

namespace Hindman168
open scoped Classical

theorem rough_balanced_box_contained {ι : Type*} (A B : ι → ℤ) (N : ℕ)
    (hN : 0 < N) (hAB : ∀ j, A j ≤ B j) (i : ι → Fin N) :
    (∀ j, A j ≤ roughBoxLower A B N i j) ∧
    (∀ j, roughBoxLower A B N i j ≤ roughBoxUpper A B N i j) ∧
    (∀ j, roughBoxUpper A B N i j ≤ B j) := by
  refine ⟨fun j => (rough_balanced_cut_contained _ _ N _ (hAB j) hN (i j).isLt.le).1,
    fun j => rough_balanced_cut_mono _ _ N (show (i j).val ≤ (i j).val+1 by omega),
    fun j => (rough_balanced_cut_contained _ _ N _ (hAB j) hN (by omega)).2⟩

theorem rough_balanced_box_side_bounds {ι : Type*} (A B : ι → ℤ) (N : ℕ)
    (hN : 0 < N) (hlen : ∀ j, 2 * (N : ℤ) ≤ B j - A j) (i : ι → Fin N) :
    ∀ j, ((B j : ℝ) - A j) / (2*N) ≤
      (roughBoxUpper A B N i j : ℝ) - roughBoxLower A B N i j ∧
      (roughBoxUpper A B N i j : ℝ) - roughBoxLower A B N i j ≤
        2 * ((B j : ℝ) - A j) / N := by
  intro j
  exact rough_balanced_cut_real_bounds _ _ N _ hN (hlen j)

theorem rough_balanced_box_scaled_sides {ι : Type*} (A B : ι → ℤ) (N : ℕ)
    (hN : 0 < N) (hlen : ∀ j, 2 * (N : ℤ) ≤ B j - A j)
    (c C Z : ℝ) (hlo : ∀ j, c*Z ≤ (B j : ℝ) - A j)
    (hhi : ∀ j, (B j : ℝ) - A j ≤ C*Z) (i : ι → Fin N) :
    ∀ j, c*Z/(2*N) ≤ (roughBoxUpper A B N i j : ℝ) - roughBoxLower A B N i j ∧
      (roughBoxUpper A B N i j : ℝ) - roughBoxLower A B N i j ≤ 2*C*Z/N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  intro j
  have hs := rough_balanced_box_side_bounds A B N hN hlen i j
  constructor
  · exact (div_le_div_of_nonneg_right (hlo j) (by positivity)).trans hs.1
  · apply hs.2.trans
    have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hhi j) (by norm_num : (0:ℝ) ≤ 2)) hNr.le
    simpa only [mul_assoc] using hh

theorem rough_balanced_box_close {ι : Type*} (A B : ι → ℤ) (N : ℕ)
    (hN : 0 < N) (hlen : ∀ j, 2 * (N : ℤ) ≤ B j - A j)
    (C Z : ℝ) (hhi : ∀ j, (B j : ℝ) - A j ≤ C*Z) (i : ι → Fin N)
    (x y : ι → ℝ)
    (hx : ∀ j, (roughBoxLower A B N i j : ℝ) ≤ x j ∧ x j ≤ roughBoxUpper A B N i j)
    (hy : ∀ j, (roughBoxLower A B N i j : ℝ) ≤ y j ∧ y j ≤ roughBoxUpper A B N i j) :
    ∀ j, |x j-y j| ≤ 2*C*Z/N := by
  intro j
  have hs := (rough_balanced_box_scaled_sides A B N hN hlen 0 C Z
    (fun j => by have hh := hlen j; have hn : (0 : ℤ) ≤ 2*N := by positivity
                 have hz : (0 : ℤ) ≤ B j-A j := hn.trans hh
                 simpa only [zero_mul] using (show (0 : ℝ) ≤ (B j : ℝ)-A j by exact_mod_cast hz)) hhi i j).2
  exact (abs_le.mpr ⟨by linarith [hx j, hy j], by linarith [hx j, hy j]⟩).trans hs

theorem rough_balanced_box_residue_nonempty {ι : Type*} [Fintype ι]
    (A B a : ι → ℤ) (N K t : ℕ) (hN : 0 < N) (hK : 0 < K) (ht : 0 < t)
    (hcop : t.Coprime K)
    (hlen : ∀ j, (2 * N * (t*K) : ℕ) ≤ (B j-A j).toNat)
    (p : (ι → Fin N) × (ι → Fin K)) :
    (alignmentBoxClass (roughBoxLower A B N p.1) (roughBoxUpper A B N p.1) a t ∩
      alignmentBoxClass (roughBoxLower A B N p.1) (roughBoxUpper A B N p.1)
        (fun j => ((p.2 j).val : ℤ)) K).Nonempty := by
  apply rough_coprime_box_piece_nonempty _ _ _ _ t K ht hK hcop
  intro j
  have hd : 2 * (t*K) ≤ (B j-A j).toNat/N :=
    (Nat.le_div_iff_mul_le hN).mpr (by nlinarith [hlen j])
  have hs := (rough_balanced_cut_step (A j) (B j) N (p.1 j).val).1
  have hdZ : (2 * (t*K) : ℤ) ≤ ((B j-A j).toNat/N : ℕ) := by exact_mod_cast hd
  exact hdZ.trans hs

end Hindman168
