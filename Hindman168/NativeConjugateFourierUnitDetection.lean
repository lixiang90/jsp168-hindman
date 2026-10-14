import Hindman168.NativeCompactFamilyUnitDetection
import Hindman168.NativeConjugateFourierObservable

/-! ACTUAL nonzero original Fourier / frozen compact parameter family
has ONE finite UNIT detector on true conjugated native data. Actual zero
Haar mean turns a genuine frozen sample mean into discrepancy. -/
namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_conjugate_fourier_unit_detection {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) (hk : k ≠ 0)
    (ρ : D.G) (K : Set D.G) (hK : IsCompact K) (δ : ℝ) (hδ : 0 < δ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := (nativeConjugateNilmanifoldData D ρ).metric
    letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) :=
      (nativeConjugateNilmanifoldData D ρ).metric.toUniformSpace.toTopologicalSpace
    ∃ θ : ℝ, 0 < θ ∧ ∃ P : Finset C(D.G ⧸ roughConjugateSubgroup D.Γ ρ,ℂ),
      (∀ J ∈ P, J ∈ unitLipschitzObservables (D.G ⧸ roughConjugateSubgroup D.Γ ρ)) ∧
      ∀ {α : Type*} (S : Finset α) (orbit : α → D.G ⧸ roughConjugateSubgroup D.Γ ρ),
        ∀ ε ∈ K, ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
          δ ≤ ‖finiteComplexSetMean S (fun n => nativeConjugateFourierObservable D L k ρ ε F (orbit n))‖ →
          ∃ J ∈ P, θ < ‖nativeNilmanifoldFiniteDiscrepancy (nativeConjugateNilmanifoldData D ρ) S orbit J‖ := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := (nativeConjugateNilmanifoldData D ρ).metric
  letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) :=
    (nativeConjugateNilmanifoldData D ρ).metric.toUniformSpace.toTopologicalSpace
  let H := (fun p : D.G × C(D.G ⧸ D.Γ,ℂ) => nativeConjugateFourierObservable D L k ρ p.1 p.2) ''
    (K ×ˢ unitLipschitzObservables (D.G ⧸ D.Γ))
  have hH : IsCompact H := native_conjugate_fourier_observable_family_compact D L k ρ K hK
  obtain ⟨θ,hθ,P,hP,hDetect⟩ := native_compact_family_unit_detection (nativeConjugateNilmanifoldData D ρ) δ hδ H hH
  refine ⟨θ,hθ,P,hP,?_⟩
  intro α S orbit ε hε F hF hMean
  apply hDetect S orbit (nativeConjugateFourierObservable D L k ρ ε F)
    ⟨(ε,F),⟨hε,hF⟩,rfl⟩
  change δ ≤ ‖finiteComplexSetMean S (fun n => nativeConjugateFourierObservable D L k ρ ε F (orbit n))-
    ∫ q, nativeConjugateFourierObservable D L k ρ ε F q
      ∂nativeNilmanifoldQuotientProbability (nativeConjugateNilmanifoldData D ρ)‖
  rw [native_conjugate_fourier_observable_zero_mean D L k ρ ε hk F,sub_zero]
  exact hMean

end Hindman168
