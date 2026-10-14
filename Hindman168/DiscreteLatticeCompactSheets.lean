import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Algebra.Group.Compact

/-! Genuine finite lattice intersections with compact sets bound all sheets
meeting a compact group set from a relatively compact original section. -/

namespace Hindman168
open Set
open scoped Pointwise

theorem discrete_lattice_compact_intersection_finite {G : Type*} [Group G] [TopologicalSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] (hΓ : IsClosed (Γ : Set G))
    (C : Set G) (hC : IsCompact C) : {γ : Γ | (γ : G) ∈ C}.Finite :=
  (hΓ.isClosedEmbedding_subtypeVal.isCompact_preimage hC).finite_of_discrete

theorem coset_section_compact_sheet_membership {G : Type*} [Group G]
    (Γ : Subgroup G) (τ : (G ⧸ Γ) → G) (K C : Set G) (hK : Set.range τ ⊆ K)
    (q : G ⧸ Γ) (γ : Γ) (hC : τ q*(γ : G) ∈ C) : (γ : G) ∈ K⁻¹*C := by
  apply Set.mem_mul.mpr
  refine ⟨(τ q)⁻¹, ?_, τ q*(γ : G), hC, ?_⟩
  · have hk : τ q ∈ K := hK ⟨q,rfl⟩
    exact Set.mem_inv.mpr (by simpa only [inv_inv] using hk)
  · exact inv_mul_cancel_left _ _

theorem coset_section_compact_sheets_finite {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (Γ : Subgroup G) [DiscreteTopology Γ] (hΓ : IsClosed (Γ : Set G))
    (K C : Set G) (hK : IsCompact K) (hC : IsCompact C) :
    {γ : Γ | (γ : G) ∈ K⁻¹*C}.Finite :=
  discrete_lattice_compact_intersection_finite Γ hΓ _ (hK.inv.mul hC)

end Hindman168
