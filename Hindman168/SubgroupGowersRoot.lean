import Hindman168.SubgroupCubePositive
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Nonnegative roots of the actual positive-dimensional cube means.
The identities here do not assert a triangle inequality. -/
namespace Hindman168
open scoped BigOperators
variable {G : Type*} [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]

noncomputable def subgroupGowersValue (d : ℕ) (h : G → ℝ) : ℝ :=
  (subgroupCubeAverage Q d h) ^ ((2 ^ d : ℕ)⁻¹ : ℝ)

theorem subgroupGowersValue_nonneg (d : ℕ) (hd : 0 < d) (h : G → ℝ) :
    0 ≤ subgroupGowersValue Q d h :=
  Real.rpow_nonneg (subgroupCubeAverage_nonneg Q d hd h) _

theorem subgroupGowersValue_pow (d : ℕ) (hd : 0 < d) (h : G → ℝ) :
    subgroupGowersValue Q d h ^ (2 ^ d) = subgroupCubeAverage Q d h :=
  Real.rpow_inv_natCast_pow (subgroupCubeAverage_nonneg Q d hd h) (pow_ne_zero _ (by decide))

theorem subgroupGowersValue_le_one (d : ℕ) (hd : 0 < d) (h : G → ℝ)
    (hh : ∀ x, |h x| ≤ 1) : subgroupGowersValue Q d h ≤ 1 :=
  Real.rpow_le_one (subgroupCubeAverage_nonneg Q d hd h)
    ((le_abs_self _).trans (subgroupCubeAverage_abs_le_one Q d h hh)) (by positivity)

noncomputable def weightedSubgroupGowersValue {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (d : ℕ) (h : ι → G → ℝ) : ℝ :=
  (weightedSubgroupCubeAverage p Q d h) ^ ((2 ^ d : ℕ)⁻¹ : ℝ)

theorem weightedSubgroupGowersValue_nonneg {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ c, 0 ≤ p c) (d : ℕ) (hd : 0 < d) (h : ι → G → ℝ) :
    0 ≤ weightedSubgroupGowersValue Q p d h :=
  Real.rpow_nonneg (weightedSubgroupCubeAverage_nonneg Q p hp d hd h) _

theorem weightedSubgroupGowersValue_pow {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ c, 0 ≤ p c) (d : ℕ) (hd : 0 < d) (h : ι → G → ℝ) :
    weightedSubgroupGowersValue Q p d h ^ (2 ^ d) =
      ∑ c, p c * subgroupGowersValue Q d (h c) ^ (2 ^ d) := by
  rw [weightedSubgroupGowersValue,
    Real.rpow_inv_natCast_pow (weightedSubgroupCubeAverage_nonneg Q p hp d hd h)
      (pow_ne_zero _ (by decide))]
  simp only [subgroupGowersValue_pow Q d hd, weightedSubgroupCubeAverage]

theorem weightedSubgroupGowersValue_le_one {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ c, 0 ≤ p c) (hsum : ∑ c, p c = 1)
    (d : ℕ) (hd : 0 < d) (h : ι → G → ℝ) (hh : ∀ c x, |h c x| ≤ 1) :
    weightedSubgroupGowersValue Q p d h ≤ 1 :=
  Real.rpow_le_one (weightedSubgroupCubeAverage_nonneg Q p hp d hd h)
    ((le_abs_self _).trans (weightedSubgroupCubeAverage_abs_le_one p hp hsum Q d h hh))
    (by positivity)

end Hindman168
