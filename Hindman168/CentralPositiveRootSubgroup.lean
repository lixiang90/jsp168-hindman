import Hindman168.PositiveSubgroupRoots
import Mathlib.GroupTheory.Subgroup.Center

/-! Actual roots of the specified subgroup inside the actual center
form a genuine subgroup. Closure uses commuting-root multiplication
in the original group, not general root-saturation closure. -/

namespace Hindman168

variable {G : Type*} [Group G]

def centralPositiveRootSubgroup (Γ : Subgroup G) : Subgroup G where
  carrier := positiveSubgroupRoots Γ ∩ (Subgroup.center G : Set G)
  one_mem' := ⟨subgroup_mem_positiveRoots Γ Γ.one_mem, (Subgroup.center G).one_mem⟩
  mul_mem' := by
    intro g h hg hh
    refine ⟨positiveSubgroupRoots_mul_of_commute Γ hg.1 hh.1 ?_,
      (Subgroup.center G).mul_mem hg.2 hh.2⟩
    exact (Subgroup.mem_center_iff.mp hg.2 h).symm
  inv_mem' := fun hg => ⟨positiveSubgroupRoots_inv Γ hg.1,
    (Subgroup.center G).inv_mem hg.2⟩

theorem centralPositiveRootSubgroup_mem_iff (Γ : Subgroup G) (g : G) :
    g ∈ centralPositiveRootSubgroup Γ ↔
      g ∈ positiveSubgroupRoots Γ ∧ g ∈ Subgroup.center G := Iff.rfl

theorem centralPositiveRootSubgroup_le_center (Γ : Subgroup G) :
    centralPositiveRootSubgroup Γ ≤ Subgroup.center G := fun _ hg => hg.2

theorem center_intersection_le_positiveRootSubgroup (Γ : Subgroup G) :
    Γ ⊓ Subgroup.center G ≤ centralPositiveRootSubgroup Γ :=
  fun _ hg => ⟨subgroup_mem_positiveRoots Γ hg.1, hg.2⟩

end Hindman168
