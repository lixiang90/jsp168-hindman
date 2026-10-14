import Hindman168.CentralSubgroupFactorMap
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Basic

/-! Actual central-subgroup factor pushforward preserves probability,
quotient-group invariance and continuous integrals. No lattice normality. -/

namespace Hindman168
open MeasureTheory
variable {G : Type*} [Group G] (N Γ : Subgroup G) [N.Normal]

theorem central_subgroup_factor_map_equivariant (g : G) (q : G ⧸ Γ) :
    centralSubgroupFactorMap N Γ (g • q) = (g : G ⧸ N) • centralSubgroupFactorMap N Γ q := by
  induction q using Quotient.inductionOn with
  | _ h => rfl

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)]

noncomputable def centralSubgroupFactorProbability (μ : Measure (G ⧸ Γ)) :
    @Measure ((G ⧸ N) ⧸ Γ.map (QuotientGroup.mk' N)) (borel ((G ⧸ N) ⧸ Γ.map (QuotientGroup.mk' N))) := by
  letI : MeasurableSpace ((G ⧸ N) ⧸ Γ.map (QuotientGroup.mk' N)) := borel ((G ⧸ N) ⧸ Γ.map (QuotientGroup.mk' N))
  exact Measure.map (centralSubgroupFactorMap N Γ) μ

theorem central_subgroup_factor_probability_isProbability (μ : Measure (G ⧸ Γ)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (centralSubgroupFactorProbability N Γ μ) := by
  letI : MeasurableSpace ((G ⧸ N) ⧸ Γ.map (QuotientGroup.mk' N)) := borel ((G ⧸ N) ⧸ Γ.map (QuotientGroup.mk' N))
  letI : BorelSpace ((G ⧸ N) ⧸ Γ.map (QuotientGroup.mk' N)) := ⟨rfl⟩
  exact Measure.isProbabilityMeasure_map (central_subgroup_factor_map_openQuotient N Γ).continuous.measurable.aemeasurable

theorem central_subgroup_factor_probability_integral (μ : Measure (G ⧸ Γ))
    (F : C((G ⧸ N) ⧸ Γ.map (QuotientGroup.mk' N), ℂ)) :
    (∫ y, F y ∂centralSubgroupFactorProbability N Γ μ) = ∫ q, F (centralSubgroupFactorMap N Γ q) ∂μ := by
  letI : MeasurableSpace ((G ⧸ N) ⧸ Γ.map (QuotientGroup.mk' N)) := borel ((G ⧸ N) ⧸ Γ.map (QuotientGroup.mk' N))
  letI : BorelSpace ((G ⧸ N) ⧸ Γ.map (QuotientGroup.mk' N)) := ⟨rfl⟩
  exact integral_map (central_subgroup_factor_map_openQuotient N Γ).continuous.measurable.aemeasurable
    F.continuous.aestronglyMeasurable

theorem central_subgroup_factor_probability_translate (μ : Measure (G ⧸ Γ))
    (hμ : ∀ g : G, Measure.map (fun q : G ⧸ Γ => g • q) μ = μ) (h : G ⧸ N) :
    letI : MeasurableSpace ((G ⧸ N) ⧸ Γ.map (QuotientGroup.mk' N)) := borel ((G ⧸ N) ⧸ Γ.map (QuotientGroup.mk' N))
    Measure.map (fun y => h • y) (centralSubgroupFactorProbability N Γ μ) = centralSubgroupFactorProbability N Γ μ := by
  letI : MeasurableSpace ((G ⧸ N) ⧸ Γ.map (QuotientGroup.mk' N)) := borel ((G ⧸ N) ⧸ Γ.map (QuotientGroup.mk' N))
  letI : BorelSpace ((G ⧸ N) ⧸ Γ.map (QuotientGroup.mk' N)) := ⟨rfl⟩
  obtain ⟨g,rfl⟩ := QuotientGroup.mk_surjective h
  have hg : Measurable (fun q : G ⧸ Γ => g • q) := (continuous_const_smul g).measurable
  have hh : Measurable (fun y : (G ⧸ N) ⧸ Γ.map (QuotientGroup.mk' N) => (g : G ⧸ N) • y) :=
    (continuous_const_smul (g : G ⧸ N)).measurable
  have hp := (central_subgroup_factor_map_openQuotient N Γ).continuous.measurable
  have he : (fun y : (G ⧸ N) ⧸ Γ.map (QuotientGroup.mk' N) => (g : G ⧸ N) • y) ∘ centralSubgroupFactorMap N Γ =
      centralSubgroupFactorMap N Γ ∘ (fun q : G ⧸ Γ => g • q) := by
    funext q
    exact (central_subgroup_factor_map_equivariant N Γ g q).symm
  change Measure.map _ (Measure.map _ _) = Measure.map _ _
  rw [Measure.map_map hh hp,he,← Measure.map_map hp hg,hμ]

end Hindman168
