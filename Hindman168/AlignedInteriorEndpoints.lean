import Hindman168.AlignedIntervalResiduePartition

namespace Hindman168

theorem alignedInterior_endpoint_bounds (A B : ℤ) (R : ℕ) (hR : 0 < R) :
    A ≤ (A / R + 1) * R ∧ (A / R + 1) * R ≤ A + R ∧
    B - R ≤ (B / R) * R ∧ (B / R) * R ≤ B := by
  have hp : (0 : ℤ) < R := by exact_mod_cast hR
  have ha := Int.emod_nonneg A (ne_of_gt hp)
  have hb := Int.emod_nonneg B (ne_of_gt hp)
  have ha' := Int.emod_lt_of_pos A hp
  have hb' := Int.emod_lt_of_pos B hp
  have ea := Int.mul_ediv_add_emod A (R : ℤ)
  have eb := Int.mul_ediv_add_emod B (R : ℤ)
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem alignedInterior_ordered (A B : ℤ) (R : ℕ) (hR : 0 < R)
    (hgap : A + 2 * R ≤ B) : (A / R + 1) * R ≤ (B / R) * R := by
  obtain ⟨_, ha, hb, _⟩ := alignedInterior_endpoint_bounds A B R hR
  linarith

theorem alignedInterior_deleted_subset (A B : ℤ) (R : ℕ) (hR : 0 < R) :
    Finset.Ico A B \ Finset.Ico ((A / R + 1) * R) ((B / R) * R) ⊆
      Finset.Ico A (A + R) ∪ Finset.Ico (B - R) B := by
  intro y hy
  obtain ⟨hy, hn⟩ := Finset.mem_sdiff.mp hy
  obtain ⟨hay, hyb⟩ := Finset.mem_Ico.mp hy
  have he := alignedInterior_endpoint_bounds A B R hR
  apply Finset.mem_union.mpr
  by_cases hl : y < (A / R + 1) * R
  · exact Or.inl (Finset.mem_Ico.mpr ⟨hay, hl.trans_le he.2.1⟩)
  · have hu : (B / R) * R ≤ y := by
      by_contra h
      exact hn (Finset.mem_Ico.mpr ⟨le_of_not_gt hl, lt_of_not_ge h⟩)
    exact Or.inr (Finset.mem_Ico.mpr ⟨he.2.2.1.trans hu, hyb⟩)

theorem alignedInterior_deleted_card (A B : ℤ) (R : ℕ) (hR : 0 < R) :
    (Finset.Ico A B \ Finset.Ico ((A / R + 1) * R) ((B / R) * R)).card ≤ 2 * R := by
  calc
    _ ≤ (Finset.Ico A (A + R) ∪ Finset.Ico (B - R) B).card :=
      Finset.card_le_card (alignedInterior_deleted_subset A B R hR)
    _ ≤ (Finset.Ico A (A + R)).card + (Finset.Ico (B - R) B).card := Finset.card_union_le _ _
    _ = 2 * R := by simp [Int.card_Ico]; omega

end Hindman168

