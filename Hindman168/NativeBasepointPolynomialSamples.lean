import Hindman168.NativeBasepointTrimmedPolynomial
import Hindman168.NativeBasepointObservable
import Hindman168.NativeCentralPolynomialProjection
import Hindman168.NativeNilmanifoldFiniteDiscrepancy
import Hindman168.NativeCompactCosetRepresentatives

/-! EXACT original multivariate integer coset samples and genuine original
canonical discrepancies under actual compact basepoint normalization. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_basepoint_polynomial_original_orbit {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E) (r : D.G)
    (γ : D.Γ) (hr : nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) p 0) = r * γ) (x : σ → ℤ) :
    r • nativeMvPolynomialOrbit D (nativeBasepointPolynomial D p r) x = nativeMvPolynomialOrbit D p x := by
  change (QuotientGroup.mk (r * nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
    (roughVectorMvEval (E := D.E) (nativeBasepointPolynomial D p r) (fun i => (x i : ℝ)))) : D.G ⧸ D.Γ) = _
  rw [native_basepoint_polynomial_exp]
  exact rough_group_basepoint_normalization_original_coset D.Γ
    (fun y : σ → ℝ => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) p y)) r γ hr (fun i => (x i : ℝ))

theorem native_basepoint_polynomial_original_sample {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E) (r : D.G)
    (γ : D.Γ) (hr : nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) p 0) = r * γ) (x : σ → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ,ℂ),
      nativeBasepointObservable D r F (nativeMvPolynomialOrbit D (nativeBasepointPolynomial D p r) x) =
        F (nativeMvPolynomialOrbit D p x) := by
  intro F
  rw [native_basepoint_observable_apply,native_basepoint_polynomial_original_orbit D p r γ hr]

theorem native_basepoint_polynomial_original_discrepancy {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E) (r : D.G)
    (γ : D.Γ) (hr : nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) p 0) = r * γ) (a : Finset (σ → ℤ)) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ,ℂ),
      nativeNilmanifoldFiniteDiscrepancy D a (nativeMvPolynomialOrbit D (nativeBasepointPolynomial D p r))
        (nativeBasepointObservable D r F) =
      nativeNilmanifoldFiniteDiscrepancy D a (nativeMvPolynomialOrbit D p) F := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  change finiteComplexSetMean a (fun x => nativeBasepointObservable D r F
    (nativeMvPolynomialOrbit D (nativeBasepointPolynomial D p r) x)) -
    (∫ q, nativeBasepointObservable D r F q ∂nativeNilmanifoldQuotientProbability D) = _
  rw [native_basepoint_observable_canonical_integral]
  have he : (fun x => nativeBasepointObservable D r F
      (nativeMvPolynomialOrbit D (nativeBasepointPolynomial D p r) x)) =
      (fun x => F (nativeMvPolynomialOrbit D p x)) := by
    funext x
    exact native_basepoint_polynomial_original_sample D p r γ hr x F
  rw [he]
  rfl

theorem native_basepoint_polynomial_fixed_representatives {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) :
    ∃ K : Set D.G, IsCompact K ∧ ∀ {σ : Type*} (p : RoughVectorMvPolynomial σ D.E),
      ∃ r ∈ K, ∃ γ : D.Γ, nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (roughVectorMvEval (E := D.E) p 0) = r * γ := by
  obtain ⟨K,hK,hRep⟩ := native_exists_compact_coset_representatives D
  refine ⟨K,hK,?_⟩
  intro σ p
  exact hRep _

end Hindman168
