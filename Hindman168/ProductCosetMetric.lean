import Hindman168.ProductCosetQuotient
import Mathlib.Topology.MetricSpace.Isometry

/-! The product quotient metric is transported along the NATURAL coset
equivalence. Compatibility with the original quotient topology follows
whenever the two given factor metrics have their original quotient maps. -/

namespace Hindman168

variable {G H : Type*} [Group G] [Group H] (Γ : Subgroup G) (Λ : Subgroup H)
  [MetricSpace (G ⧸ Γ)] [MetricSpace (H ⧸ Λ)]

@[implicit_reducible]
noncomputable def productCosetMetric : MetricSpace ((G × H) ⧸ Γ.prod Λ) :=
  MetricSpace.induced (productCosetMap Γ Λ) (productCosetMap_bijective Γ Λ).injective inferInstance

noncomputable def productCosetIsometryEquiv :
    letI := productCosetMetric Γ Λ
    ((G × H) ⧸ Γ.prod Λ) ≃ᵢ (G ⧸ Γ) × (H ⧸ Λ) :=
  letI := productCosetMetric Γ Λ
  { toEquiv := productCosetEquiv Γ Λ, isometry_toFun := fun _ _ => rfl }

theorem productCosetMetric_compact [CompactSpace (G ⧸ Γ)] [CompactSpace (H ⧸ Λ)] :
    letI := productCosetMetric Γ Λ
    CompactSpace ((G × H) ⧸ Γ.prod Λ) := by
  letI := productCosetMetric Γ Λ
  exact (productCosetIsometryEquiv Γ Λ).toHomeomorph.symm.compactSpace

theorem productCosetMetric_quotientMap [TopologicalSpace G] [TopologicalSpace H]
    (hΓ : @IsOpenQuotientMap G (G ⧸ Γ) inferInstance
      (inferInstance : MetricSpace (G ⧸ Γ)).toUniformSpace.toTopologicalSpace (↑))
    (hΛ : @IsOpenQuotientMap H (H ⧸ Λ) inferInstance
      (inferInstance : MetricSpace (H ⧸ Λ)).toUniformSpace.toTopologicalSpace (↑)) :
    @IsOpenQuotientMap (G × H) ((G × H) ⧸ Γ.prod Λ) inferInstance
      (productCosetMetric Γ Λ).toUniformSpace.toTopologicalSpace (↑) := by
  letI : TopologicalSpace (G ⧸ Γ) := (inferInstance : MetricSpace (G ⧸ Γ)).toUniformSpace.toTopologicalSpace
  letI : TopologicalSpace (H ⧸ Λ) := (inferInstance : MetricSpace (H ⧸ Λ)).toUniformSpace.toTopologicalSpace
  letI := productCosetMetric Γ Λ
  letI : TopologicalSpace ((G × H) ⧸ Γ.prod Λ) := (productCosetMetric Γ Λ).toUniformSpace.toTopologicalSpace
  have h := (productCosetIsometryEquiv Γ Λ).toHomeomorph.symm.isOpenQuotientMap.comp (hΓ.prodMap hΛ)
  have he : (productCosetIsometryEquiv Γ Λ).symm ∘
      (fun p : G × H => ((p.1 : G ⧸ Γ), (p.2 : H ⧸ Λ))) =
      ((↑) : G × H → (G × H) ⧸ Γ.prod Λ) := by
    funext p
    exact (productCosetEquiv Γ Λ).symm_apply_apply (p : (G × H) ⧸ Γ.prod Λ)
  exact he ▸ h

theorem productCosetMetric_topology_eq [TopologicalSpace G] [TopologicalSpace H]
    (hΓ : @IsOpenQuotientMap G (G ⧸ Γ) inferInstance
      (inferInstance : MetricSpace (G ⧸ Γ)).toUniformSpace.toTopologicalSpace (↑))
    (hΛ : @IsOpenQuotientMap H (H ⧸ Λ) inferInstance
      (inferInstance : MetricSpace (H ⧸ Λ)).toUniformSpace.toTopologicalSpace (↑)) :
    (productCosetMetric Γ Λ).toUniformSpace.toTopologicalSpace =
      QuotientGroup.instTopologicalSpace (Γ.prod Λ) := by
  letI : TopologicalSpace (G ⧸ Γ) := (inferInstance : MetricSpace (G ⧸ Γ)).toUniformSpace.toTopologicalSpace
  letI : TopologicalSpace (H ⧸ Λ) := (inferInstance : MetricSpace (H ⧸ Λ)).toUniformSpace.toTopologicalSpace
  letI : TopologicalSpace ((G × H) ⧸ Γ.prod Λ) := (productCosetMetric Γ Λ).toUniformSpace.toTopologicalSpace
  exact (productCosetMetric_quotientMap Γ Λ hΓ hΛ).isQuotientMap.isCoinducing.eq_coinduced

end Hindman168
