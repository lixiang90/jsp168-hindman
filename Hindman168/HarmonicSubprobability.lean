import Hindman168.HarmonicDilation

/-! The original harmonic law is a subprobability at every stage,
including a zero normalizer. No replacement or repaired law is used. -/

namespace Hindman168
open FiniteMass
open scoped BigOperators

theorem harmonicNormalizer_nonnegative (X W : ℕ) : 0 ≤ harmonicNormalizer X W :=
  Finset.sum_nonneg (fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n))

theorem integerMass_eq_zero_of_normalizer_zero (X W : ℕ)
    (hZ : harmonicNormalizer X W = 0) : integerMass X W = 0 := by
  ext z
  by_cases hz : 0 ≤ z
  · rw [Int.eq_natCast_toNat.mpr hz, integerMass_apply_nat]
    simp [harmonicWeight, hZ]
  · rw [integerMass_apply_of_neg X W (lt_of_not_ge hz)]
    rfl

theorem integerMass_nonnegative (X W : ℕ) (z : ℤ) : 0 ≤ integerMass X W z := by
  rcases (harmonicNormalizer_nonnegative X W).eq_or_lt with hz | hz
  · rw [integerMass_eq_zero_of_normalizer_zero X W hz.symm]
    rfl
  · exact integerMass_nonneg hz z

theorem integerMass_total_zero_or_one (X W : ℕ) :
    total (integerMass X W) = 0 ∨ total (integerMass X W) = 1 := by
  rcases (harmonicNormalizer_nonnegative X W).eq_or_lt with hz | hz
  · left
    rw [integerMass_eq_zero_of_normalizer_zero X W hz.symm]
    simp [total]
  · exact Or.inr (integerMass_total hz)

theorem integerMass_total_le_one (X W : ℕ) : total (integerMass X W) ≤ 1 := by
  rcases integerMass_total_zero_or_one X W with h | h
  · rw [h]; norm_num
  · rw [h]

instance integerMass_nonnegFact (X W : ℕ) : Fact (∀ z, 0 ≤ integerMass X W z) :=
  ⟨integerMass_nonnegative X W⟩

end Hindman168

