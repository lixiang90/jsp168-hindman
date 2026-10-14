import Mathlib.Topology.Algebra.Group.Quotient

/-! Actual image-lattice discreteness is preserved under PROVED equality
of the ORIGINAL normal subgroups. Original lattice need not be normal. -/

namespace Hindman168
variable {G : Type*} [Group G] [TopologicalSpace G]

theorem subgroup_quotient_lattice_discrete_of_eq (N M Γ : Subgroup G) [N.Normal] [M.Normal]
    (h : N=M) (hN : DiscreteTopology (Γ.map (QuotientGroup.mk' N))) :
    DiscreteTopology (Γ.map (QuotientGroup.mk' M)) := by
  cases h
  exact hN

end Hindman168
