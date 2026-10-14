import Hindman168.DiagonalCenterSubgroup

/-! ACTUAL original diagonal center is closed in the ORIGINAL product
topology. No diagonal quotient lattice discreteness or step drop is assumed. -/

namespace Hindman168
variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

theorem diagonal_center_closed : IsClosed ((diagonalCenterSubgroup G) : Set (G × G)) := by
  have he : ((diagonalCenterSubgroup G) : Set (G × G)) =
      {p | p.1 = p.2 ∧ ∀ g : G, g*p.1 = p.1*g} := by
    ext p
    constructor
    · intro hp
      obtain ⟨z,rfl⟩ := (diagonal_center_mem_iff G p).mp hp
      exact ⟨rfl,fun g => Subgroup.mem_center_iff.mp z.property g⟩
    · intro hp
      apply (diagonal_center_mem_iff G p).mpr
      exact ⟨⟨p.1,Subgroup.mem_center_iff.mpr hp.2⟩,Prod.ext rfl hp.1.symm⟩
  rw [he]
  have hc : IsClosed {p : G × G | ∀ g : G, g*p.1 = p.1*g} := by
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro g
    exact isClosed_eq (continuous_const.mul continuous_fst) (continuous_fst.mul continuous_const)
  exact (isClosed_eq continuous_fst continuous_snd).inter hc

end Hindman168
