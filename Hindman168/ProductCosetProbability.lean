import Hindman168.ProductCosetQuotient
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Group.Measure

/-! Actual product of invariant probabilities on original NONNORMAL
cosets, transported through the genuine product coset homeomorphism. -/

namespace Hindman168
open MeasureTheory
variable {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H] (Γ : Subgroup G) (Λ : Subgroup H)
  [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)] [SecondCountableTopology (G ⧸ Γ)]
  [MeasurableSpace (H ⧸ Λ)] [BorelSpace (H ⧸ Λ)] [SecondCountableTopology (H ⧸ Λ)]

omit [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
  [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)] [SecondCountableTopology (G ⧸ Γ)]
  [MeasurableSpace (H ⧸ Λ)] [BorelSpace (H ⧸ Λ)] [SecondCountableTopology (H ⧸ Λ)] in
theorem product_coset_map_action (g : G) (h : H) (q : (G × H) ⧸ Γ.prod Λ) :
    productCosetMap Γ Λ ((g,h) • q) =
      (g • (productCosetMap Γ Λ q).1,h • (productCosetMap Γ Λ q).2) := by
  induction q using Quotient.inductionOn with
  | _ p => rfl

noncomputable def productCosetProbability (μ : Measure (G ⧸ Γ)) (ν : Measure (H ⧸ Λ)) :
    @Measure ((G × H) ⧸ Γ.prod Λ) (borel ((G × H) ⧸ Γ.prod Λ)) := by
  letI : MeasurableSpace ((G × H) ⧸ Γ.prod Λ) := borel ((G × H) ⧸ Γ.prod Λ)
  exact Measure.map (productCosetHomeomorph Γ Λ).symm (μ.prod ν)

omit [SecondCountableTopology (G ⧸ Γ)] in
theorem product_coset_probability_isProbability (μ : Measure (G ⧸ Γ)) (ν : Measure (H ⧸ Λ))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (productCosetProbability Γ Λ μ ν) := by
  letI : MeasurableSpace ((G × H) ⧸ Γ.prod Λ) := borel ((G × H) ⧸ Γ.prod Λ)
  letI : BorelSpace ((G × H) ⧸ Γ.prod Λ) := ⟨rfl⟩
  exact Measure.isProbabilityMeasure_map (productCosetHomeomorph Γ Λ).symm.measurable.aemeasurable

omit [SecondCountableTopology (G ⧸ Γ)] in
theorem product_coset_probability_map (μ : Measure (G ⧸ Γ)) (ν : Measure (H ⧸ Λ)) :
    letI : MeasurableSpace ((G × H) ⧸ Γ.prod Λ) := borel ((G × H) ⧸ Γ.prod Λ)
    Measure.map (productCosetMap Γ Λ) (productCosetProbability Γ Λ μ ν) = μ.prod ν := by
  letI : MeasurableSpace ((G × H) ⧸ Γ.prod Λ) := borel ((G × H) ⧸ Γ.prod Λ)
  letI : BorelSpace ((G × H) ⧸ Γ.prod Λ) := ⟨rfl⟩
  exact (productCosetHomeomorph Γ Λ).toMeasurableEquiv.map_map_symm

omit [SecondCountableTopology (G ⧸ Γ)] in
theorem product_coset_probability_translate (μ : Measure (G ⧸ Γ)) (ν : Measure (H ⧸ Λ))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ g : G, Measure.map (fun q : G ⧸ Γ => g • q) μ = μ)
    (hν : ∀ h : H, Measure.map (fun r : H ⧸ Λ => h • r) ν = ν) (g : G) (h : H) :
    letI : MeasurableSpace ((G × H) ⧸ Γ.prod Λ) := borel ((G × H) ⧸ Γ.prod Λ)
    Measure.map (fun q : (G × H) ⧸ Γ.prod Λ => (g,h) • q) (productCosetProbability Γ Λ μ ν) =
      productCosetProbability Γ Λ μ ν := by
  letI : MeasurableSpace ((G × H) ⧸ Γ.prod Λ) := borel ((G × H) ⧸ Γ.prod Λ)
  letI : BorelSpace ((G × H) ⧸ Γ.prod Λ) := ⟨rfl⟩
  let e := productCosetHomeomorph Γ Λ
  have hg : Measurable (fun q : G ⧸ Γ => g • q) := (continuous_const_smul g).measurable
  have hh : Measurable (fun q : H ⧸ Λ => h • q) := (continuous_const_smul h).measurable
  have hp : Measurable (fun q : (G × H) ⧸ Γ.prod Λ => (g,h) • q) := (continuous_const_smul (g,h)).measurable
  have he : (fun q : (G × H) ⧸ Γ.prod Λ => (g,h) • q) ∘ e.symm =
      e.symm ∘ Prod.map (fun q : G ⧸ Γ => g • q) (fun q : H ⧸ Λ => h • q) := by
    funext p
    apply e.injective
    change productCosetMap Γ Λ ((g,h) • e.symm p) =
      productCosetMap Γ Λ (e.symm (Prod.map (fun q => g • q) (fun q => h • q) p))
    rw [product_coset_map_action]
    change (g • (e (e.symm p)).1,h • (e (e.symm p)).2) =
      e (e.symm (Prod.map (fun q => g • q) (fun q => h • q) p))
    simp only [Homeomorph.apply_symm_apply]
    cases p
    rfl
  change Measure.map _ (Measure.map e.symm _) = Measure.map e.symm _
  rw [Measure.map_map hp e.symm.measurable,he,← Measure.map_map e.symm.measurable (hg.prodMap hh),
    ← Measure.map_prod_map μ ν hg hh,hμ,hν]

end Hindman168
