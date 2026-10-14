import Hindman168.AlignedInteriorEndpoints
import Hindman168.HarmonicSubprobability

namespace Hindman168
open scoped BigOperators

theorem integerMass_le_reciprocal_lower (X W : ℕ) (hX : 0 < X)
    (hZ : 0 < harmonicNormalizer X W) (y : ℤ) (hy : (X : ℤ) ≤ y) :
    integerMass X W y ≤ (1 / (X : ℝ)) / harmonicNormalizer X W := by
  have hn : 0 ≤ y := (Int.natCast_nonneg X).trans hy
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  have hx : (0 : ℝ) < X := by exact_mod_cast hX
  have hxy : (X : ℝ) ≤ n := by exact_mod_cast hy
  rw [integerMass_apply_nat, harmonicWeight]
  split_ifs
  · apply div_le_div_of_nonneg_right _ hZ.le
    simpa only [one_div] using one_div_le_one_div_of_le hx hxy
  · positivity

theorem alignedInterior_deleted_integerMass_le (X W R : ℕ) (hX : 0 < X) (hR : 0 < R)
    (hZ : 0 < harmonicNormalizer X W) :
    (∑ y ∈ Finset.Ico (X : ℤ) (X ^ 2 : ℕ) \
      Finset.Ico (((X : ℤ) / R + 1) * R) (((X ^ 2 : ℕ) : ℤ) / R * R),
      integerMass X W y) ≤ (2 * R : ℕ) * ((1 / (X : ℝ)) / harmonicNormalizer X W) := by
  let D := Finset.Ico (X : ℤ) (X ^ 2 : ℕ) \
    Finset.Ico (((X : ℤ) / R + 1) * R) (((X ^ 2 : ℕ) : ℤ) / R * R)
  change (∑ y ∈ D, integerMass X W y) ≤ _
  calc
    _ ≤ ∑ _y ∈ D, ((1 / (X : ℝ)) / harmonicNormalizer X W) := by
      apply Finset.sum_le_sum
      intro y hy
      exact integerMass_le_reciprocal_lower X W hX hZ y
        (Finset.mem_Ico.mp (Finset.mem_sdiff.mp hy).1).1
    _ = (D.card : ℝ) * ((1 / (X : ℝ)) / harmonicNormalizer X W) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast alignedInterior_deleted_card (X : ℤ) (X ^ 2 : ℕ) R hR)
      (by positivity)

end Hindman168
