import Hindman168.WeightedHaarHilbert
import Hindman168.SubgroupGowersRoot

namespace Hindman168
open scoped BigOperators Classical
universe u

/-- All actual data of a finite weighted subgroup system. The three finite
types and their sizes are part of the data, not fixed parameters of a bound. -/
structure FiniteWeightedSubgroupSystem where
  G : Type u
  addCommGroup : AddCommGroup G
  finiteGroup : Fintype G
  κ : Type u
  finiteCells : Fintype κ
  A : Type u
  finiteIndices : Fintype A
  p : κ → ℝ
  p_nonneg : ∀ c, 0 ≤ p c
  p_total : @Finset.sum κ ℝ _ (@Finset.univ κ finiteCells) p = 1
  α : A → ℝ
  α_nonneg : ∀ a, 0 ≤ α a
  α_total : @Finset.sum A ℝ _ (@Finset.univ A finiteIndices) α = 1
  Q : A → @AddSubgroup G addCommGroup.toAddGroup
  g : κ → G → ℝ
  g_unit : ∀ c x, |g c x| ≤ 1

attribute [instance] FiniteWeightedSubgroupSystem.addCommGroup
  FiniteWeightedSubgroupSystem.finiteGroup FiniteWeightedSubgroupSystem.finiteCells
  FiniteWeightedSubgroupSystem.finiteIndices

/-- The mean over the original direction law, without repeated-index
approximation or a changed cell law. -/
noncomputable def finiteWeightedSubgroupMean (S : FiniteWeightedSubgroupSystem) (d : ℕ) : ℝ :=
  ∑ a, S.α a * weightedSubgroupGowersValue (S.Q a) S.p d S.g

/-- The independent pair mean over the same original direction law. -/
noncomputable def finiteWeightedSubgroupPairMean (S : FiniteWeightedSubgroupSystem) (d : ℕ) : ℝ :=
  ∑ a, ∑ b, S.α a * S.α b * weightedSubgroupGowersValue (S.Q a ⊔ S.Q b) S.p d S.g

theorem finiteWeightedSubgroupMean_nonneg (S : FiniteWeightedSubgroupSystem)
    (d : ℕ) (hd : 0 < d) : 0 ≤ finiteWeightedSubgroupMean S d :=
  Finset.sum_nonneg (fun a _ => mul_nonneg (S.α_nonneg a)
    (weightedSubgroupGowersValue_nonneg (S.Q a) S.p S.p_nonneg d hd S.g))

theorem finiteWeightedSubgroupMean_le_one (S : FiniteWeightedSubgroupSystem)
    (d : ℕ) (hd : 0 < d) : finiteWeightedSubgroupMean S d ≤ 1 := by
  calc
    _ ≤ ∑ a, S.α a * 1 := Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left
      (weightedSubgroupGowersValue_le_one (S.Q a) S.p S.p_nonneg S.p_total d hd S.g S.g_unit)
      (S.α_nonneg a))
    _ = _ := by simpa only [mul_one] using S.α_total

theorem finiteWeightedSubgroupPairMean_nonneg (S : FiniteWeightedSubgroupSystem)
    (d : ℕ) (hd : 0 < d) : 0 ≤ finiteWeightedSubgroupPairMean S d :=
  Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ =>
    mul_nonneg (mul_nonneg (S.α_nonneg a) (S.α_nonneg b))
      (weightedSubgroupGowersValue_nonneg (S.Q a ⊔ S.Q b) S.p S.p_nonneg d hd S.g)))

end Hindman168
