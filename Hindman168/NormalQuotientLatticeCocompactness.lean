import Hindman168.SubgroupQuotientImageMap

/-! Actual original coset compactness descends to the specified lattice
image under the genuine quotient homomorphism. Normality of the lattice
is unnecessary; normality is only required of the subgroup being removed. -/

namespace Hindman168

variable {G : Type*} [Group G] [TopologicalSpace G]

theorem normalQuotient_lattice_image_cocompact (Γ N : Subgroup G) [N.Normal]
    [CompactSpace (G ⧸ Γ)] :
    CompactSpace ((G ⧸ N) ⧸ Γ.map (QuotientGroup.mk' N)) :=
  subgroupQuotientImageMap_compactSpace (QuotientGroup.mk' N) Γ
    QuotientGroup.continuous_mk (QuotientGroup.mk'_surjective N)

end Hindman168
