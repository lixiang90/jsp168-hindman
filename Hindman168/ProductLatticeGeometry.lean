import Hindman168.ProductCosetQuotient
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.GroupTheory.Nilpotent

/-! Product closure preserves the original discrete lattices, compact
coset spaces and the common nilpotence-step bound. -/

namespace Hindman168

variable {G H : Type*} [Group G] [Group H] (Γ : Subgroup G) (Λ : Subgroup H)

theorem productLattice_discrete [TopologicalSpace G] [TopologicalSpace H]
    [DiscreteTopology Γ] [DiscreteTopology Λ] : DiscreteTopology (Γ.prod Λ) :=
  (Homeomorph.Set.prod (Γ : Set G) (Λ : Set H)).isEmbedding.discreteTopology

theorem productLattice_quotient_compact [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    [CompactSpace (G ⧸ Γ)] [CompactSpace (H ⧸ Λ)] : CompactSpace ((G × H) ⧸ Γ.prod Λ) :=
  (productCosetHomeomorph Γ Λ).symm.compactSpace

omit Γ Λ in
theorem productGroup_nilpotencyClass_le [Group.IsNilpotent G] [Group.IsNilpotent H]
    (s : ℕ) (hG : Group.nilpotencyClass G ≤ s) (hH : Group.nilpotencyClass H ≤ s) :
    Group.nilpotencyClass (G × H) ≤ s := by
  rw [Group.nilpotencyClass_prod]
  exact max_le hG hH

end Hindman168
