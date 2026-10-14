import Hindman168.SubgroupCubeAverage
import Hindman168.WeightedSubgroupCombination

/-! The previous coprime-pair bound instantiated with actual subgroup
cube averages, retaining both tuple probabilities and cell probabilities. -/
namespace Hindman168
open scoped BigOperators Classical

theorem weighted_subgroup_cube_combination {G ι κ : Type*}
    [AddCommGroup G] [Fintype G] [Fintype ι] [Fintype κ]
    (p : ι → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) (q : ι → ℕ)
    (α : κ → ℝ) (hα : ∀ c, 0 ≤ α c) (hαsum : ∑ c, α c = 1)
    (d : ℕ) (h : κ → G → ℝ) (hh : ∀ c x, |h c x| ≤ 1) :
    (∑ a, ∑ b, p a * p b * |weightedSubgroupCubeAverage α
      (multipleAddSubgroup G (q a) ⊔ multipleAddSubgroup G (q b)) d h|) ≤
      |weightedSubgroupCubeAverage α (⊤ : AddSubgroup G) d h| +
        ∑ a, ∑ b, p a * p b * (if (q a).Coprime (q b) then 0 else 1) := by
  exact weighted_multiple_subgroup_bound p hp hsum q
    (fun Q => |weightedSubgroupCubeAverage α Q d h|) (abs_nonneg _)
    (fun Q => weightedSubgroupCubeAverage_abs_le_one α hα hαsum Q d h hh)

end Hindman168
