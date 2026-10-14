import Hindman168.RoughConjugateRightCosetEquiv
import Mathlib.Topology.MetricSpace.Isometry

/-! Actual original compatible quotient metric is pulled back through
the TRUE right-coset equivalence; the new metric quotient map is PROVED. -/
namespace Hindman168
variable {G : Type*} [Group G] (Γ : Subgroup G) (g : G) [MetricSpace (G ⧸ Γ)]

@[implicit_reducible]
noncomputable def roughConjugateRightCosetMetric : MetricSpace (G ⧸ roughConjugateSubgroup Γ g) :=
  MetricSpace.induced (roughConjugateRightCosetMap Γ g)
    (roughConjugateRightCosetEquiv Γ g).injective inferInstance

noncomputable def roughConjugateRightCosetIsometryEquiv :
    letI := roughConjugateRightCosetMetric Γ g
    (G ⧸ roughConjugateSubgroup Γ g) ≃ᵢ (G ⧸ Γ) :=
  letI := roughConjugateRightCosetMetric Γ g
  { toEquiv := roughConjugateRightCosetEquiv Γ g, isometry_toFun := fun _ _ => rfl }

theorem rough_conjugate_right_coset_metric_quotientMap [TopologicalSpace G] [IsTopologicalGroup G]
    (hΓ : @IsOpenQuotientMap G (G ⧸ Γ) inferInstance
      (inferInstance : MetricSpace (G ⧸ Γ)).toUniformSpace.toTopologicalSpace (↑)) :
    @IsOpenQuotientMap G (G ⧸ roughConjugateSubgroup Γ g) inferInstance
      (roughConjugateRightCosetMetric Γ g).toUniformSpace.toTopologicalSpace (↑) := by
  letI : TopologicalSpace (G ⧸ Γ) := (inferInstance : MetricSpace (G ⧸ Γ)).toUniformSpace.toTopologicalSpace
  letI := roughConjugateRightCosetMetric Γ g
  letI : TopologicalSpace (G ⧸ roughConjugateSubgroup Γ g) :=
    (roughConjugateRightCosetMetric Γ g).toUniformSpace.toTopologicalSpace
  have h := (roughConjugateRightCosetIsometryEquiv Γ g).toHomeomorph.symm.isOpenQuotientMap.comp
    (hΓ.comp (Homeomorph.mulRight g).isOpenQuotientMap)
  have he : (roughConjugateRightCosetIsometryEquiv Γ g).symm ∘
      ((↑) : G → G ⧸ Γ) ∘ (Homeomorph.mulRight g) =
      ((↑) : G → G ⧸ roughConjugateSubgroup Γ g) := by
    funext x
    change ((x*g)*g⁻¹ : G ⧸ roughConjugateSubgroup Γ g)=(x : G ⧸ roughConjugateSubgroup Γ g)
    rw [mul_inv_cancel_right]
  exact he ▸ h

theorem rough_conjugate_right_coset_metric_topology [TopologicalSpace G] [IsTopologicalGroup G]
    (hΓ : @IsOpenQuotientMap G (G ⧸ Γ) inferInstance
      (inferInstance : MetricSpace (G ⧸ Γ)).toUniformSpace.toTopologicalSpace (↑)) :
    (roughConjugateRightCosetMetric Γ g).toUniformSpace.toTopologicalSpace=
      QuotientGroup.instTopologicalSpace (roughConjugateSubgroup Γ g) := by
  letI : TopologicalSpace (G ⧸ Γ) := (inferInstance : MetricSpace (G ⧸ Γ)).toUniformSpace.toTopologicalSpace
  letI := roughConjugateRightCosetMetric Γ g
  letI : TopologicalSpace (G ⧸ roughConjugateSubgroup Γ g) :=
    (roughConjugateRightCosetMetric Γ g).toUniformSpace.toTopologicalSpace
  exact (rough_conjugate_right_coset_metric_quotientMap Γ g hΓ).isQuotientMap.isCoinducing.eq_coinduced

end Hindman168
