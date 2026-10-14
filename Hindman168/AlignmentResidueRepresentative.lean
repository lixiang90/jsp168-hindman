import Hindman168.AlignmentIntegerResidues

/-! The bounded solution is unique and chosen from q, t and L alone.
Consequently fixing those data modulo L fixes the actual residue shift. -/

namespace Hindman168
open scoped Classical

noncomputable def alignmentResidueRepresentative (q t L : ℕ) : ℕ :=
  if h : 0 < L ∧ Nat.Coprime t L then
    Classical.choose (Nat.exists_mul_mod_eq_of_coprime q h.2 h.1.ne')
  else 0

theorem alignmentResidueRepresentative_spec {q t L : ℕ}
    (hL : 0 < L) (ht : Nat.Coprime t L) :
    alignmentResidueRepresentative q t L < L ∧
      Nat.ModEq L (t * alignmentResidueRepresentative q t L) q := by
  unfold alignmentResidueRepresentative
  rw [dif_pos ⟨hL, ht⟩]
  exact Classical.choose_spec (Nat.exists_mul_mod_eq_of_coprime q ht hL.ne')

theorem alignment_bounded_residue_unique {q t L ρ σ : ℕ}
    (ht : Nat.Coprime t L) (hρ : ρ < L) (hσ : σ < L)
    (hcρ : Nat.ModEq L (t * ρ) q) (hcσ : Nat.ModEq L (t * σ) q) : ρ = σ := by
  exact (Nat.ModEq.cancel_left_of_coprime ht.symm (hcρ.trans hcσ.symm)).eq_of_lt_of_lt hρ hσ

theorem alignmentResidueRepresentative_eq {q t L ρ : ℕ}
    (hL : 0 < L) (ht : Nat.Coprime t L) (hρ : ρ < L)
    (hcρ : Nat.ModEq L (t * ρ) q) : alignmentResidueRepresentative q t L = ρ := by
  obtain ⟨hσ, hcσ⟩ := alignmentResidueRepresentative_spec hL ht (q := q)
  exact alignment_bounded_residue_unique ht hσ hρ hcσ hcρ

theorem alignmentResidueRepresentative_congr {q q' t t' L : ℕ}
    (hL : 0 < L) (ht : Nat.Coprime t L) (ht' : Nat.Coprime t' L)
    (htcong : Nat.ModEq L t t') (hqcong : Nat.ModEq L q q') :
    alignmentResidueRepresentative q t L = alignmentResidueRepresentative q' t' L := by
  obtain ⟨hρ, hcρ⟩ := alignmentResidueRepresentative_spec hL ht (q := q)
  obtain ⟨hσ, hcσ⟩ := alignmentResidueRepresentative_spec hL ht' (q := q')
  have hc : Nat.ModEq L (t * alignmentResidueRepresentative q' t' L) q :=
    ((htcong.mul_right _).trans hcσ).trans hqcong.symm
  exact alignment_bounded_residue_unique ht hρ hσ hcρ hc

end Hindman168
