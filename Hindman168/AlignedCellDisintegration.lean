import Hindman168.HarmonicShortCubeGowersBound

namespace Hindman168
open scoped BigOperators

theorem alignedInterval_completeCell_mass_pos (X W M q : ℕ) (hX : 0 < X)
    (hM : 0 < M) (hq : 0 < q) (hWM : W ∣ M) (hZ : 0 < harmonicNormalizer X W)
    (a b : ℤ) (hlo : (X : ℤ) ≤ a * (M * q : ℕ)) (hhi : b * (M * q : ℕ) ≤ (X ^ 2 : ℕ))
    (k : ℤ) (hk : k ∈ Finset.Ico a b) (r : Fin M) (hr : r.val.Coprime W) :
    0 < ∑ y ∈ intervalResidueSet (k * (M * q : ℕ)) (M * q) M r.val, integerMass X W y := by
  obtain ⟨hak, hkb⟩ := Finset.mem_Ico.mp hk
  have hl := hlo.trans (mul_le_mul_of_nonneg_right hak (Int.natCast_nonneg (M * q)))
  have hk1 : k + 1 ≤ b := by omega
  have hu := (mul_le_mul_of_nonneg_right hk1 (Int.natCast_nonneg (M * q))).trans hhi
  rw [add_mul, one_mul] at hu
  have hx : (0 : ℝ) < X := by exact_mod_cast hX
  have hleft : (X : ℝ) ≤ (k : ℝ) * (M * q : ℕ) := by exact_mod_cast hl
  exact completeResidueCell_integerMass_pos X W k M q hM hq hWM r hr hZ hl hu (hx.trans_le hleft)

theorem alignedInterval_conditional_disintegration (X W M q : ℕ) (hX : 0 < X)
    (hM : 0 < M) (hq : 0 < q) (hWM : W ∣ M) (hZ : 0 < harmonicNormalizer X W)
    (a b : ℤ) (hlo : (X : ℤ) ≤ a * (M * q : ℕ)) (hhi : b * (M * q : ℕ) ≤ (X ^ 2 : ℕ))
    (f : ℤ → ℝ) :
    let cell := fun k (r : Fin M) => intervalResidueSet (k * (M * q : ℕ)) (M * q) M r.val
    let mass := fun k r => ∑ y ∈ cell k r, integerMass X W y
    let total := ∑ y ∈ Finset.Ico (a * (M * q : ℕ)) (b * (M * q : ℕ)), integerMass X W y
    (∑ k ∈ Finset.Ico a b, ∑ r ∈ (Finset.univ : Finset (Fin M)).filter (fun r => r.val.Coprime W),
      (mass k r / total) * ((∑ y ∈ cell k r, integerMass X W y * f y) / mass k r)) =
    (∑ y ∈ Finset.Ico (a * (M * q : ℕ)) (b * (M * q : ℕ)), integerMass X W y * f y) / total := by
  intro cell mass total
  have he : ∀ k ∈ Finset.Ico a b, ∀ r ∈ (Finset.univ : Finset (Fin M)).filter (fun r => r.val.Coprime W),
      (mass k r / total) * ((∑ y ∈ cell k r, integerMass X W y * f y) / mass k r) =
        (∑ y ∈ cell k r, integerMass X W y * f y) / total := by
    intro k hk r hr
    have hm : mass k r ≠ 0 := ne_of_gt (alignedInterval_completeCell_mass_pos X W M q hX hM hq hWM hZ
      a b hlo hhi k hk r (Finset.mem_filter.mp hr).2)
    rw [div_mul_div_comm, mul_comm total (mass k r), mul_div_mul_left _ _ hm]
  calc
    _ = ∑ k ∈ Finset.Ico a b, ∑ r ∈ (Finset.univ : Finset (Fin M)).filter (fun r => r.val.Coprime W),
        (∑ y ∈ cell k r, integerMass X W y * f y) / total := by
      apply Finset.sum_congr rfl
      intro k hk
      exact Finset.sum_congr rfl (fun r hr => he k hk r hr)
    _ = _ := by
      simp_rw [← Finset.sum_div]
      rw [← alignedInterval_admissible_cell_sum X W M q hM hq hWM a b hlo hhi f]

end Hindman168
