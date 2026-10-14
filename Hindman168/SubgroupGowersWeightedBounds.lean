import Hindman168.SubgroupGowersRoot
import Hindman168.WeightedMomentThreshold
import Hindman168.WeightedSubgroupCombination

/-! The paper's cell-mass lower bound and coprime-subgroup estimate for
the actual nonnegative Gowers roots, not only their powers. -/
namespace Hindman168
open scoped BigOperators Classical

theorem subgroupGowers_good_cell_mass {G ι : Type*} [AddCommGroup G] [Fintype G] [Fintype ι]
    (Q : AddSubgroup G) [Fintype Q] (p : ι → ℝ) (hp : ∀ c, 0 ≤ p c)
    (hsum : ∑ c, p c = 1) (d : ℕ) (hd : 0 < d)
    (h : ι → G → ℝ) (hh : ∀ c x, |h c x| ≤ 1)
    (δ : ℝ) (hδ : 0 ≤ δ) (hglobal : δ ≤ weightedSubgroupGowersValue Q p d h) :
    δ ^ (2 ^ d) / 2 ≤ ∑ c, if δ / 2 ≤ subgroupGowersValue Q d (h c) then p c else 0 := by
  apply weighted_power_half_mass p (fun c => subgroupGowersValue Q d (h c)) hp hsum
    (fun c => ⟨subgroupGowersValue_nonneg Q d hd (h c), subgroupGowersValue_le_one Q d hd (h c) (hh c)⟩)
    (2 ^ d) (pow_pos (by decide) _) δ hδ
  rw [← weightedSubgroupGowersValue_pow Q p hp d hd h]
  exact pow_le_pow_left₀ hδ hglobal _

theorem weighted_subgroup_gowers_combination {G ι κ : Type*}
    [AddCommGroup G] [Fintype G] [Fintype ι] [Fintype κ]
    (p : ι → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) (q : ι → ℕ)
    (α : κ → ℝ) (hα : ∀ c, 0 ≤ α c) (hαsum : ∑ c, α c = 1)
    (d : ℕ) (hd : 0 < d) (h : κ → G → ℝ) (hh : ∀ c x, |h c x| ≤ 1) :
    (∑ a, ∑ b, p a * p b * weightedSubgroupGowersValue
      (multipleAddSubgroup G (q a) ⊔ multipleAddSubgroup G (q b)) α d h) ≤
      weightedSubgroupGowersValue (⊤ : AddSubgroup G) α d h +
        ∑ a, ∑ b, p a * p b * (if (q a).Coprime (q b) then 0 else 1) :=
  weighted_multiple_subgroup_bound p hp hsum q
    (fun Q => weightedSubgroupGowersValue Q α d h)
    (weightedSubgroupGowersValue_nonneg _ α hα d hd h)
    (fun Q => weightedSubgroupGowersValue_le_one Q α hα hαsum d hd h hh)

end Hindman168
