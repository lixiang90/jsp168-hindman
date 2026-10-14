import Hindman168.MasterAlignedInteriorMass

namespace Hindman168
open scoped BigOperators

theorem inadmissible_completeCell_sum_zero (X W M q : ℕ) (hM : 0 < M) (hWM : W ∣ M)
    (k : ℤ) (r : Fin M) (hr : ¬ r.val.Coprime W)
    (hlo : (X : ℤ) ≤ k * (M * q : ℕ))
    (hhi : k * (M * q : ℕ) + (M * q : ℕ) ≤ (X ^ 2 : ℕ)) (f : ℤ → ℝ) :
    (∑ y ∈ intervalResidueSet (k * (M * q : ℕ)) (M * q) M r.val,
      integerMass X W y * f y) = 0 := by
  rw [completeResidueCell_integerMass_sum X W k M q hM hWM r hlo hhi f, if_neg hr]

theorem alignedInterval_admissible_cell_sum (X W M q : ℕ) (hM : 0 < M) (hq : 0 < q)
    (hWM : W ∣ M) (a b : ℤ) (hlo : (X : ℤ) ≤ a * (M * q : ℕ))
    (hhi : b * (M * q : ℕ) ≤ (X ^ 2 : ℕ)) (f : ℤ → ℝ) :
    (∑ y ∈ Finset.Ico (a * (M * q : ℕ)) (b * (M * q : ℕ)), integerMass X W y * f y) =
      ∑ k ∈ Finset.Ico a b, ∑ r ∈ (Finset.univ : Finset (Fin M)).filter (fun r => r.val.Coprime W),
        ∑ y ∈ intervalResidueSet (k * (M * q : ℕ)) (M * q) M r.val, integerMass X W y * f y := by
  classical
  rw [alignedInterval_residue_sum (M * q) M (Nat.mul_pos hM hq) hM a b]
  apply Finset.sum_congr rfl
  intro k hk
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro r _ hr
  have hbad : ¬ r.val.Coprime W := by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hr
  obtain ⟨hak, hkb⟩ := Finset.mem_Ico.mp hk
  apply inadmissible_completeCell_sum_zero X W M q hM hWM k r hbad
  · exact hlo.trans (mul_le_mul_of_nonneg_right hak (Int.natCast_nonneg _))
  · have hk1 : k + 1 ≤ b := by omega
    have he := mul_le_mul_of_nonneg_right hk1 (Int.natCast_nonneg (M * q))
    rw [add_mul, one_mul] at he
    exact he.trans hhi

theorem alignedInterval_cell_probability_sum (X W M q : ℕ) (hM : 0 < M) (hq : 0 < q)
    (hWM : W ∣ M) (a b : ℤ) (hlo : (X : ℤ) ≤ a * (M * q : ℕ))
    (hhi : b * (M * q : ℕ) ≤ (X ^ 2 : ℕ))
    (hp : 0 < ∑ y ∈ Finset.Ico (a * (M * q : ℕ)) (b * (M * q : ℕ)), integerMass X W y) :
    (∑ k ∈ Finset.Ico a b, ∑ r ∈ (Finset.univ : Finset (Fin M)).filter (fun r => r.val.Coprime W),
      (∑ y ∈ intervalResidueSet (k * (M * q : ℕ)) (M * q) M r.val, integerMass X W y) /
      (∑ y ∈ Finset.Ico (a * (M * q : ℕ)) (b * (M * q : ℕ)), integerMass X W y)) = 1 := by
  have he := alignedInterval_admissible_cell_sum X W M q hM hq hWM a b hlo hhi (fun _ => 1)
  simp only [mul_one] at he
  simp_rw [← Finset.sum_div]
  rw [← he, div_self (ne_of_gt hp)]

theorem integerMass_cell_probability_nonneg (X W : ℕ) (S T : Finset ℤ)
    (hp : 0 < ∑ y ∈ T, integerMass X W y) :
    0 ≤ (∑ y ∈ S, integerMass X W y) / (∑ y ∈ T, integerMass X W y) :=
  div_nonneg (Finset.sum_nonneg (fun y _ => integerMass_nonnegative X W y)) hp.le

end Hindman168
