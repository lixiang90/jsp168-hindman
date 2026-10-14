import Hindman168.SubgroupQuotientImageMap

/-! The genuine image-lattice factor for a normal subgroup. Original
lattice cosets remain nonnormal; the normality is only that of N. -/

namespace Hindman168
variable {G : Type*} [Group G] (N Γ : Subgroup G) [N.Normal]

def centralSubgroupFactorMap : (G ⧸ Γ) → ((G ⧸ N) ⧸ Γ.map (QuotientGroup.mk' N)) :=
  subgroupQuotientImageMap (QuotientGroup.mk' N) Γ

theorem central_subgroup_factor_map_mk (g : G) :
    centralSubgroupFactorMap N Γ (g : G ⧸ Γ) =
      ((g : G ⧸ N) : (G ⧸ N) ⧸ Γ.map (QuotientGroup.mk' N)) := rfl

theorem central_subgroup_factor_map_surjective : Function.Surjective (centralSubgroupFactorMap N Γ) :=
  subgroupQuotientImageMap_surjective _ Γ (QuotientGroup.mk'_surjective N)

theorem central_subgroup_factor_map_invariant (z : N) (q : G ⧸ Γ) :
    centralSubgroupFactorMap N Γ ((z : G) • q) = centralSubgroupFactorMap N Γ q := by
  induction q using Quotient.inductionOn with
  | _ g =>
    change (((z : G)*g : G ⧸ N) : (G ⧸ N) ⧸ Γ.map (QuotientGroup.mk' N)) = _
    rw [(QuotientGroup.eq_one_iff (z : G)).mpr z.property, one_mul]
    rfl

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem central_subgroup_factor_map_openQuotient : IsOpenQuotientMap (centralSubgroupFactorMap N Γ) := by
  apply (QuotientGroup.isOpenQuotientMap_mk (N := Γ)).of_comp_iff.mp
  exact (QuotientGroup.isOpenQuotientMap_mk (N := Γ.map (QuotientGroup.mk' N))).comp
    (QuotientGroup.isOpenQuotientMap_mk (N := N))

omit [IsTopologicalGroup G] in
theorem central_subgroup_factor_compact [CompactSpace (G ⧸ Γ)] :
    CompactSpace ((G ⧸ N) ⧸ Γ.map (QuotientGroup.mk' N)) :=
  subgroupQuotientImageMap_compactSpace _ Γ QuotientGroup.continuous_mk (QuotientGroup.mk'_surjective N)

end Hindman168
