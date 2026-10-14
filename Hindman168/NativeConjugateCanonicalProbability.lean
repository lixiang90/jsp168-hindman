import Hindman168.NativeConjugateNilmanifoldData
import Hindman168.NativeNilmanifoldProbabilityUniqueness

/-! TRUE right-coset homeomorphism transports ACTUAL conjugated native
canonical probability to ORIGINAL canonical probability. Genuine left
equivariance and invariant-probability uniqueness prove Haar agreement. -/
namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_conjugate_right_canonical_probability {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (ρ : D.G) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    Measure.map (roughConjugateRightCosetMap D.Γ ρ)
      (nativeNilmanifoldQuotientProbability (nativeConjugateNilmanifoldData D ρ))=
        nativeNilmanifoldQuotientProbability D := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  let D' := nativeConjugateNilmanifoldData D ρ
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_coset_borel D
  letI : BorelSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := native_nilmanifold_coset_borel D'
  let e := roughConjugateRightCosetHomeomorph D.Γ ρ
  let μ : Measure (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := nativeNilmanifoldQuotientProbability D'
  let ν := Measure.map e μ
  letI : IsProbabilityMeasure μ := native_nilmanifold_quotient_probability_isProbability D'
  have hProbability : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (μ := μ) e.measurable.aemeasurable
  have hInvariant : ∀ g : D.G, Measure.map (fun q : D.G ⧸ D.Γ => g • q) ν=ν := by
    intro g
    have hLeft : Measurable (fun q : D.G ⧸ D.Γ => g • q) :=
      (continuous_const_smul g).measurable
    have hChild : Measurable (fun q : D.G ⧸ roughConjugateSubgroup D.Γ ρ => g • q) :=
      (continuous_const_smul g).measurable
    have hAction : (fun q : D.G ⧸ D.Γ => g • q) ∘ e=
        e ∘ (fun q : D.G ⧸ roughConjugateSubgroup D.Γ ρ => g • q) := by
      funext q
      exact (rough_conjugate_right_coset_equivariant D.Γ ρ g q).symm
    change Measure.map _ (Measure.map e μ)=Measure.map e μ
    rw [Measure.map_map hLeft e.measurable,hAction,← Measure.map_map e.measurable hChild]
    have hTranslate := native_nilmanifold_quotient_probability_translate D' g
    exact congrArg (Measure.map e) hTranslate
  exact native_nilmanifold_invariant_probability_unique D ν hProbability hInvariant

theorem native_conjugate_right_canonical_integral {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (ρ : D.G) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    ∀ F : (D.G ⧸ D.Γ) → ℂ,
      (∫ q, F (roughConjugateRightCosetMap D.Γ ρ q)
        ∂nativeNilmanifoldQuotientProbability (nativeConjugateNilmanifoldData D ρ))=
          ∫ q, F q ∂nativeNilmanifoldQuotientProbability D := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_coset_borel D
  letI : BorelSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) :=
    native_nilmanifold_coset_borel (nativeConjugateNilmanifoldData D ρ)
  intro F
  rw [← native_conjugate_right_canonical_probability D ρ]
  exact ((roughConjugateRightCosetHomeomorph D.Γ ρ).measurableEmbedding.integral_map F).symm

end Hindman168
