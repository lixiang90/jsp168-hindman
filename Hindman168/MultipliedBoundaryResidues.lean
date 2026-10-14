import Hindman168.NilDivisorBoundary

/-! Periodic boundary residues for the actual product t*p. Multiplication
by t embeds these residues into the retained joint boundary set. No
coprimality of t with the interval length is required. -/

namespace Hindman168

open scoped BigOperators Classical

noncomputable def multipliedBoundaryResidues (W t H B : ℕ) : Finset ℕ :=
  (Finset.range (W * H)).filter (fun p => p.Coprime W ∧
    ¬ intervalInteriorRoot H B ((t * p : ℕ) : ℤ))

theorem multipliedBoundaryResidues_subset (W t H B : ℕ) :
    multipliedBoundaryResidues W t H B ⊆ Finset.range (W * H) := Finset.filter_subset _ _

theorem multipliedBoundaryResidues_mem_mod (W t H B p : ℕ) (hW : 0 < W) (hH : 0 < H) :
    p % (W * H) ∈ multipliedBoundaryResidues W t H B ↔
      p.Coprime W ∧ ¬ intervalInteriorRoot H B ((t * p : ℕ) : ℤ) := by
  have hc : (p % (W * H)).Coprime W ↔ p.Coprime W := by
    change (p % (W * H)).gcd W = 1 ↔ p.gcd W = 1
    rw [((Nat.mod_modEq p (W * H)).of_mul_right H).gcd_eq]
  have hm : (t * (p % (W * H))) % H = (t * p) % H := by
    rw [Nat.mul_mod, Nat.mod_mod_of_dvd p (dvd_mul_left H W), ← Nat.mul_mod]
  have hi : intervalInteriorRoot H B ((t * (p % (W * H)) : ℕ) : ℤ) ↔
      intervalInteriorRoot H B ((t * p : ℕ) : ℤ) := by
    simp only [intervalInteriorRoot, ← Int.natCast_mod, hm]
  simp only [multipliedBoundaryResidues, Finset.mem_filter, Finset.mem_range,
    Nat.mod_lt p (Nat.mul_pos hW hH), true_and, hc, hi]

theorem multipliedBoundaryResidues_card_le_joint {W t H B : ℕ}
    (hW : 0 < W) (ht : 0 < t) (hco : W.Coprime t) :
    (multipliedBoundaryResidues W t H B).card ≤
      (jointBoundaryResidues H B (W * t) (unitResidues W t 0)).card := by
  have hinj : Function.Injective (fun p : ℕ => t * p) :=
    fun _ _ h => Nat.eq_of_mul_eq_mul_left ht h
  rw [← Finset.card_image_of_injective _ hinj]
  apply Finset.card_le_card
  intro y hy
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨hpRange, hc, hb⟩ := Finset.mem_filter.mp hp
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr ?_, ?_, hb⟩
  · have hh := Nat.mul_lt_mul_of_pos_left (Finset.mem_range.mp hpRange) ht
    simpa only [Nat.mul_assoc, Nat.mul_left_comm] using hh
  · exact (unitResidues_mem_mod W t (t * p) hW ht).mpr
      ⟨Nat.coprime_mul_iff_left.mpr ⟨hco.symm, hc⟩, dvd_mul_right t p⟩

theorem multipliedBoundaryResidues_card_bound {W t H B d : ℕ}
    (hW : 0 < W) (ht : 0 < t) (hH : 0 < H) (hco : W.Coprime t) (hB : B ≤ d * H) :
    ((multipliedBoundaryResidues W t H B).card : ℝ) ≤
      (W.totient : ℝ) * (2 * B + (W * t : ℕ) * (2 + 4 * (d : ℝ))) := by
  have hc := jointBoundaryResidues_card_bound H B (W * t) d hH (Nat.mul_pos hW ht)
    hB (unitResidues W t 0) (Finset.filter_subset _ _)
  rw [unitResidues_card hW ht hco ht] at hc
  exact (show ((multipliedBoundaryResidues W t H B).card : ℝ) ≤
    (jointBoundaryResidues H B (W * t) (unitResidues W t 0)).card by
      exact_mod_cast multipliedBoundaryResidues_card_le_joint hW ht hco).trans hc

theorem multipliedBoundaryResidues_card_total {W t H B : ℕ}
    (hW : 0 < W) (ht : 0 < t) (hco : W.Coprime t) :
    ((multipliedBoundaryResidues W t H B).card : ℝ) ≤ (W.totient : ℝ) * ((H : ℝ) + 1) := by
  have hc := jointBoundaryResidues_card_total_bound H B (W * t) (Nat.mul_pos hW ht)
    (unitResidues W t 0) (Finset.filter_subset _ _)
  rw [unitResidues_card hW ht hco ht] at hc
  exact (show ((multipliedBoundaryResidues W t H B).card : ℝ) ≤
    (jointBoundaryResidues H B (W * t) (unitResidues W t 0)).card by
      exact_mod_cast multipliedBoundaryResidues_card_le_joint hW ht hco).trans hc

end Hindman168
