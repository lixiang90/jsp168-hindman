import Hindman168.RationalLinearDenominators

/-! Clear rational denominators using a positive natural multiplier
inside the actual original integer submodule. The converse gives the
exact rational-span membership characterization. -/

namespace Hindman168
open Submodule

variable {E : Type*} [AddCommGroup E] [Module ℚ E]

theorem rationalSpan_positive_nat_multiple (L : Submodule ℤ E) {x : E}
    (hx : x ∈ span ℚ (L : Set E)) :
    ∃ n : ℕ, 0 < n ∧ n • x ∈ L := by
  obtain ⟨n, hn, hnx⟩ := rationalSpan_integer_multiple L hx
  refine ⟨n.natAbs, Int.natAbs_pos.mpr hn, ?_⟩
  have he : ((n.natAbs : ℤ) • x) = n.natAbs • x := by simp only [natCast_zsmul]
  rw [← he]
  by_cases h : 0 ≤ n
  · simpa only [Int.natCast_natAbs, abs_of_nonneg h] using hnx
  · simpa only [Int.natCast_natAbs, abs_of_neg (lt_of_not_ge h), neg_smul] using L.neg_mem hnx

theorem rationalSpan_mem_iff_positive_nat_multiple (L : Submodule ℤ E) (x : E) :
    x ∈ span ℚ (L : Set E) ↔ ∃ n : ℕ, 0 < n ∧ n • x ∈ L := by
  constructor
  · exact rationalSpan_positive_nat_multiple L
  · rintro ⟨n, hn, hnx⟩
    have h : n • x ∈ span ℚ (L : Set E) := subset_span hnx
    rw [← Nat.cast_smul_eq_nsmul ℚ] at h
    exact (smul_mem_iff (span ℚ (L : Set E))
      (show (n : ℚ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hn))).mp h

end Hindman168
