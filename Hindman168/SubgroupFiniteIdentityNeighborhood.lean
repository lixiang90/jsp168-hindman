import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Constructions

/-! A subgroup with a genuinely finite intersection with an open
identity neighborhood is discrete in its natural subtype topology.
Remove the actual finitely many nonidentity points from that neighborhood. -/

namespace Hindman168
open Set

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T1Space G]

 theorem subgroup_discrete_of_finite_identity_neighborhood (H : Subgroup G)
    {U : Set G} (hU : IsOpen U) (h1 : (1 : G) ∈ U)
    (hfinite : {g : G | g ∈ H ∧ g ∈ U}.Finite) : DiscreteTopology H := by
  classical
  let F : Set G := {g : G | g ∈ H ∧ g ∈ U} \ {1}
  have hF : F.Finite := hfinite.sdiff
  have hUF : IsOpen (U \ F) := hU.sdiff hF.isClosed
  have he : ((↑) : H → G) ⁻¹' (U \ F) = {1} := by
    ext g
    constructor
    · intro hg
      apply mem_singleton_iff.mpr
      apply Subtype.ext
      by_contra hne
      exact hg.2 ⟨⟨g.property, hg.1⟩,
        by simpa only [mem_singleton_iff, Subgroup.coe_one] using hne⟩
    · intro hg
      rw [mem_singleton_iff.mp hg]
      refine ⟨h1, ?_⟩
      intro h
      exact h.2 (mem_singleton 1)
  apply discreteTopology_of_isOpen_singleton_one
  rw [← he]
  exact hUF.preimage continuous_subtype_val

end Hindman168
