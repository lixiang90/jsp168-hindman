import Hindman168.NativeConjugateRightObservable
import Hindman168.NativeRationalTerminalFourierCompactFamilies

/-! Actual original Fourier signal, frozen LEFT group parameter and TRUE
right-coset map give genuine compact families of continuous observables
on conjugated native data. Haar mean is zero for nonzero original mode.
Freezing error / short-progression selection is NOT assumed. -/
namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

noncomputable def nativeConjugateFourierObservable {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) (ρ : D.G) (ε : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := (nativeConjugateNilmanifoldData D ρ).metric
    letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) :=
      (nativeConjugateNilmanifoldData D ρ).metric.toUniformSpace.toTopologicalSpace
    C(D.G ⧸ D.Γ,ℂ) → C(D.G ⧸ roughConjugateSubgroup D.Γ ρ,ℂ) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := (nativeConjugateNilmanifoldData D ρ).metric
  letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) :=
    (nativeConjugateNilmanifoldData D ρ).metric.toUniformSpace.toTopologicalSpace
  intro F
  exact nativeConjugateRightObservable D ρ
    (nativeBasepointObservable D ε (nativeRationalTerminalFourierProjection D L k F))

theorem native_conjugate_fourier_observable_apply {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) (ρ : D.G) (ε : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := (nativeConjugateNilmanifoldData D ρ).metric
    letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) :=
      (nativeConjugateNilmanifoldData D ρ).metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ,ℂ)) (q : D.G ⧸ roughConjugateSubgroup D.Γ ρ),
      nativeConjugateFourierObservable D L k ρ ε F q=
        nativeRationalTerminalFourierProjection D L k F (ε • roughConjugateRightCosetMap D.Γ ρ q) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := (nativeConjugateNilmanifoldData D ρ).metric
  letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) :=
    (nativeConjugateNilmanifoldData D ρ).metric.toUniformSpace.toTopologicalSpace
  intro F q
  rfl

theorem native_conjugate_fourier_observable_continuous {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) (ρ : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := (nativeConjugateNilmanifoldData D ρ).metric
    letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) :=
      (nativeConjugateNilmanifoldData D ρ).metric.toUniformSpace.toTopologicalSpace
    Continuous (fun p : D.G × C(D.G ⧸ D.Γ,ℂ) => nativeConjugateFourierObservable D L k ρ p.1 p.2) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := (nativeConjugateNilmanifoldData D ρ).metric
  letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) :=
    (nativeConjugateNilmanifoldData D ρ).metric.toUniformSpace.toTopologicalSpace
  letI := native_nilmanifold_metric_quotient_compact D
  have hFourier : Continuous (nativeRationalTerminalFourierProjection D L k) :=
    (native_rational_terminal_fourier_projection_functionspace_lipschitz D L k).continuous
  exact (native_conjugate_right_observable_continuous D ρ).comp
    ((native_basepoint_observable_continuous D).comp (continuous_fst.prodMk (hFourier.comp continuous_snd)))

theorem native_conjugate_fourier_observable_family_compact {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) (ρ : D.G) (K : Set D.G) (hK : IsCompact K) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := (nativeConjugateNilmanifoldData D ρ).metric
    letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) :=
      (nativeConjugateNilmanifoldData D ρ).metric.toUniformSpace.toTopologicalSpace
    IsCompact ((fun p : D.G × C(D.G ⧸ D.Γ,ℂ) => nativeConjugateFourierObservable D L k ρ p.1 p.2) ''
      (K ×ˢ unitLipschitzObservables (D.G ⧸ D.Γ))) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := (nativeConjugateNilmanifoldData D ρ).metric
  letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) :=
    (nativeConjugateNilmanifoldData D ρ).metric.toUniformSpace.toTopologicalSpace
  exact (hK.prod (unit_lipschitz_observables_compact (D.G ⧸ D.Γ))).image
    (native_conjugate_fourier_observable_continuous D L k ρ)

theorem native_conjugate_fourier_observable_unit_bound {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) (ρ : D.G) (ε : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := (nativeConjugateNilmanifoldData D ρ).metric
    letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) :=
      (nativeConjugateNilmanifoldData D ρ).metric.toUniformSpace.toTopologicalSpace
    ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ), ∀ q : D.G ⧸ roughConjugateSubgroup D.Γ ρ,
      ‖nativeConjugateFourierObservable D L k ρ ε F q‖ ≤ 1 := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := (nativeConjugateNilmanifoldData D ρ).metric
  letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) :=
    (nativeConjugateNilmanifoldData D ρ).metric.toUniformSpace.toTopologicalSpace
  intro F hF q
  rw [native_conjugate_fourier_observable_apply,native_rational_terminal_fourier_projection_apply]
  exact torus_vertical_fourier_coefficient_bound (nativeRationalTerminalAction D L) k F
    (ε • roughConjugateRightCosetMap D.Γ ρ q) 1 hF.2

theorem native_conjugate_fourier_observable_zero_mean {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) (ρ : D.G) (ε : D.G) (hk : k ≠ 0) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := (nativeConjugateNilmanifoldData D ρ).metric
    letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) :=
      (nativeConjugateNilmanifoldData D ρ).metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ,ℂ),
      (∫ q, nativeConjugateFourierObservable D L k ρ ε F q
        ∂nativeNilmanifoldQuotientProbability (nativeConjugateNilmanifoldData D ρ))=0 := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := (nativeConjugateNilmanifoldData D ρ).metric
  letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) :=
    (nativeConjugateNilmanifoldData D ρ).metric.toUniformSpace.toTopologicalSpace
  intro F
  exact (native_conjugate_right_observable_integral D ρ _).trans
    ((native_basepoint_observable_canonical_integral D ε _).trans
      (native_rational_terminal_fourier_projection_nonzero_mean D L k hk F))

theorem native_conjugate_fourier_observable_sample {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) (ρ : D.G) (ε h : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := (nativeConjugateNilmanifoldData D ρ).metric
    letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) :=
      (nativeConjugateNilmanifoldData D ρ).metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ,ℂ),
      nativeConjugateFourierObservable D L k ρ ε F (h : D.G ⧸ roughConjugateSubgroup D.Γ ρ)=
        nativeRationalTerminalFourierProjection D L k F (ε*h*ρ : D.G ⧸ D.Γ) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := (nativeConjugateNilmanifoldData D ρ).metric
  letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) :=
    (nativeConjugateNilmanifoldData D ρ).metric.toUniformSpace.toTopologicalSpace
  intro F
  rw [native_conjugate_fourier_observable_apply,rough_conjugate_right_coset_map_mk]
  change nativeRationalTerminalFourierProjection D L k F (ε*(h*ρ) : D.G ⧸ D.Γ)=_
  rw [mul_assoc]

end Hindman168
