import Hindman168.FiniteCandidateDenseRows

namespace Hindman168
open scoped BigOperators Classical

theorem finite_bounded_candidate_density {α : Type*} (s : Finset α) (B : ℕ) (hB : 0 < B)
    (R : ℕ → α → Prop) (hR : ∀ x ∈ s, ∃ q : ℕ, 0 < q ∧ q ≤ B ∧ R q x) :
    ∃ q : ℕ, 0 < q ∧ q ≤ B ∧ (s.card : ℝ)/(B : ℝ) ≤ (s.filter (R q)).card := by
  let A := Finset.Icc 1 B
  have hA : A.Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hB⟩⟩
  have hAc : A.card = B := by simp only [A, Nat.card_Icc]; omega
  have he : s.filter (fun x => ∃ q ∈ A, R q x) = s := by
    apply Finset.filter_eq_self.mpr
    intro x hx
    obtain ⟨q, hq, hqB, hqx⟩ := hR x hx
    exact ⟨q, Finset.mem_Icc.mpr ⟨hq, hqB⟩, hqx⟩
  have ht := finite_candidate_origin_count_le_sum s A R
  rw [he] at ht
  have htr : (s.card : ℝ) ≤ ∑ q ∈ A, ((s.filter (R q)).card : ℝ) := by exact_mod_cast ht
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hbudget : (∑ _q ∈ A, (s.card : ℝ)/(B : ℝ)) ≤
      ∑ q ∈ A, ((s.filter (R q)).card : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, hAc, mul_div_cancel₀ _ hBr.ne']
    exact htr
  obtain ⟨q, hq, hqR⟩ := Finset.exists_le_of_sum_le hA hbudget
  have hbounds := Finset.mem_Icc.mp hq
  exact ⟨q, hbounds.1, hbounds.2, hqR⟩

end Hindman168
