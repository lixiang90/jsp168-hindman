import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Compactness.Compact

/-! The actual intersection of a discrete subgroup with a compact set
is finite. Closedness is derived from the actual topological group and
subgroup discreteness; it is not an additional assumption. -/

namespace Hindman168
open Set

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

 theorem discreteSubgroup_compact_inter_finite (Γ : Subgroup G) [DiscreteTopology Γ]
    {K : Set G} (hK : IsCompact K) : {g : G | g ∈ Γ ∧ g ∈ K}.Finite := by
  have hc : IsClosed (Γ : Set G) := Subgroup.isClosed_of_discrete
  have hp : IsCompact (((↑) : Γ → G) ⁻¹' K) :=
    hc.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hf := hp.finite_of_discrete.image ((↑) : Γ → G)
  have he : ((↑) : Γ → G) '' (((↑) : Γ → G) ⁻¹' K) = {g : G | g ∈ Γ ∧ g ∈ K} := by
    ext g
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.property, ha⟩
    · rintro ⟨hg, hK⟩
      exact ⟨⟨g, hg⟩, hK, rfl⟩
  rw [he] at hf
  exact hf

end Hindman168
