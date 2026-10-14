import Hindman168.SubgroupQuotientImageMap
import Hindman168.CentralCosetAction

/-! The original nonnormal coset space maps to its genuine central factor. -/

namespace Hindman168

variable {G : Type*} [Group G]

def centralFactorCosetMap (Γ : Subgroup G) :
    (G ⧸ Γ) → ((G ⧸ Subgroup.center G) ⧸ Γ.map (QuotientGroup.mk' (Subgroup.center G))) :=
  subgroupQuotientImageMap (QuotientGroup.mk' (Subgroup.center G)) Γ

theorem central_factor_coset_map_mk (Γ : Subgroup G) (g : G) :
    centralFactorCosetMap Γ (g : G ⧸ Γ) =
      ((g : G ⧸ Subgroup.center G) : (G ⧸ Subgroup.center G) ⧸
        Γ.map (QuotientGroup.mk' (Subgroup.center G))) := rfl

theorem central_factor_coset_map_surjective (Γ : Subgroup G) :
    Function.Surjective (centralFactorCosetMap Γ) :=
  subgroupQuotientImageMap_surjective _ Γ (QuotientGroup.mk'_surjective _)

theorem central_factor_coset_map_equivariant (Γ : Subgroup G) (g : G) (q : G ⧸ Γ) :
    centralFactorCosetMap Γ (g • q) =
      (g : G ⧸ Subgroup.center G) • centralFactorCosetMap Γ q := by
  induction q using Quotient.inductionOn with
  | _ h => rfl

theorem central_factor_coset_map_central (Γ : Subgroup G) (z : Subgroup.center G) (q : G ⧸ Γ) :
    centralFactorCosetMap Γ ((z : G) • q) = centralFactorCosetMap Γ q := by
  rw [central_factor_coset_map_equivariant]
  have hz : ((z : G) : G ⧸ Subgroup.center G) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr z.property
  rw [hz, one_smul]

theorem central_factor_coset_map_continuous [TopologicalSpace G] (Γ : Subgroup G) :
    Continuous (centralFactorCosetMap Γ) :=
  subgroupQuotientImageMap_continuous _ Γ QuotientGroup.continuous_mk

theorem central_factor_coset_map_openQuotient [TopologicalSpace G] [IsTopologicalGroup G]
    (Γ : Subgroup G) : IsOpenQuotientMap (centralFactorCosetMap Γ) := by
  apply (QuotientGroup.isOpenQuotientMap_mk (N := Γ)).of_comp_iff.mp
  exact (QuotientGroup.isOpenQuotientMap_mk
    (N := Γ.map (QuotientGroup.mk' (Subgroup.center G)))).comp
      (QuotientGroup.isOpenQuotientMap_mk (N := Subgroup.center G))

end Hindman168
