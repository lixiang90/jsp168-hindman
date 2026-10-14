import Hindman168.NativeAbelianTorusHaar
import Hindman168.NativeHorizontalTorusFunctional
import Hindman168.TorusMvCompactObservableInverse

/-! Genuine original abelian nilmanifold inverse, in its specified metric
and normalized invariant measure. All constants precede the polynomial,
length and unit observable; the horizontal character is actually produced. -/

namespace Hindman168
open MeasureTheory Module
open scoped Classical BigOperators Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeAbelianMvPolynomialOrbit {σ : Type*}
    (D : NativeNilmanifoldData.{u} 1) (p : RoughVectorMvPolynomial σ D.E) (x : σ → ℤ) : D.G ⧸ D.Γ :=
  (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) p (fun i => (x i : ℝ))) : D.G ⧸ D.Γ)

theorem native_abelian_mv_polynomial_torus_orbit {σ : Type*}
    (D : NativeNilmanifoldData.{u} 1) (p : RoughVectorMvPolynomial σ D.E) (x : σ → ℤ) :
    nativeAbelianMetricTorusHomeomorph D (nativeAbelianMvPolynomialOrbit D p x) =
      torusMvPolynomialOrbit (fun j : ↥(nativeFilteredHorizontalIndices (I := D.I) D.Γ) =>
        roughVectorMvProjection ((nativeLatticeFilteredSmoothRealBasis (I := D.I) D.Γ).coord j.val) p) x := by
  rw [nativeAbelianMvPolynomialOrbit, native_abelian_metric_torus_homeomorph_mk]
  funext j
  change ((nativeLatticeFilteredSmoothRealBasis (I := D.I) D.Γ).repr
    (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
      (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) p (fun i => (x i : ℝ))))) j.val :
        UnitAddCircle) = _
  rw [nativeLieGlobalLogarithm_exponential]
  change _ = ((MvPolynomial.eval (fun i => (x i : ℝ))
    (roughVectorMvProjection ((nativeLatticeFilteredSmoothRealBasis (I := D.I) D.Γ).coord j.val) p) : ℝ) : UnitAddCircle)
  rw [roughVectorMvProjection_eval]
  rfl

theorem native_abelian_finite_discrepancy_transfer {α : Type*}
    (D : NativeNilmanifoldData.{u} 1) (s : Finset α) (f : α → D.G ⧸ D.Γ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : MeasurableSpace (D.G ⧸ D.Γ) := borel (D.G ⧸ D.Γ)
    ∀ F : C(D.G ⧸ D.Γ, ℂ),
      unitTorusFiniteDiscrepancy s (fun x => nativeAbelianMetricTorusHomeomorph D (f x))
        (F.comp ⟨(nativeAbelianMetricTorusHomeomorph D).symm,
          (nativeAbelianMetricTorusHomeomorph D).symm.continuous⟩) =
      finiteComplexSetMean s (fun x => F (f x)) - ∫ q, F q ∂nativeAbelianTorusHaar D := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : MeasurableSpace (D.G ⧸ D.Γ) := borel (D.G ⧸ D.Γ)
  intro F
  change finiteComplexSetMean s (fun x => F ((nativeAbelianMetricTorusHomeomorph D).symm
    (nativeAbelianMetricTorusHomeomorph D (f x)))) - _ = _
  simp only [Homeomorph.symm_apply_apply, native_abelian_torus_haar_integral]
  rfl

theorem native_abelian_mv_polynomial_observable_inverse
    (D : NativeNilmanifoldData.{u} 1) (n d : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : MeasurableSpace (D.G ⧸ D.Γ) := borel (D.G ⧸ D.Γ)
    ∃ A : ℕ, 0 < A ∧ ∀ p : RoughVectorMvPolynomial (Fin n) D.E,
      RoughVectorMvDegreeLE p d → ∀ N : ℕ, 0 < N →
        ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
          δ ≤ ‖finiteComplexSetMean (scalarMvIntegerCube (Fin n) N)
            (fun x => F (nativeAbelianMvPolynomialOrbit D p x)) - ∫ q, F q ∂nativeAbelianTorusHaar D‖ →
          ∃ χ : D.E →L[ℝ] ℝ, RoughNativeHorizontalFunctional (I := D.I) D.Γ χ.toLinearMap ∧
            ‖χ‖ ≤ roughBasisOperatorNormBudget (nativeLatticeFilteredSmoothRealBasis (I := D.I) D.Γ)*(A : ℝ) ∧
            ∀ J : Fin n → ℕ, 0 < (∑ i, J i) →
              (N : ℝ)^(∑ i, J i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J)
                (roughVectorMvProjection χ.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : MeasurableSpace (D.G ⧸ D.Γ) := borel (D.G ⧸ D.Γ)
  let e := nativeAbelianMetricTorusHomeomorph D
  let H := (fun F : C(D.G ⧸ D.Γ, ℂ) => F.comp ⟨e.symm, e.symm.continuous⟩) ''
    unitLipschitzObservables (D.G ⧸ D.Γ)
  obtain ⟨A, hA, hinv⟩ := torus_mv_polynomial_compact_observable_inverse
    ↥(nativeFilteredHorizontalIndices (I := D.I) D.Γ) n d H
    (native_abelian_metric_observables_pullback_compact D) δ hδ
  refine ⟨A, hA, ?_⟩
  intro p hp N hN F hF hbad
  let c := fun j : ↥(nativeFilteredHorizontalIndices (I := D.I) D.Γ) =>
    roughVectorMvProjection ((nativeLatticeFilteredSmoothRealBasis (I := D.I) D.Γ).coord j.val) p
  let F' : C(UnitAddTorus ↥(nativeFilteredHorizontalIndices (I := D.I) D.Γ), ℂ) :=
    F.comp ⟨e.symm, e.symm.continuous⟩
  have hF' : F' ∈ H := ⟨F, hF, rfl⟩
  have hbad' : δ ≤ ‖unitTorusFiniteDiscrepancy (scalarMvIntegerCube (Fin n) N)
      (torusMvPolynomialOrbit c) F'‖ := by
    rw [show torusMvPolynomialOrbit c = fun x => e (nativeAbelianMvPolynomialOrbit D p x) from
      funext (fun x => (native_abelian_mv_polynomial_torus_orbit D p x).symm)]
    rw [native_abelian_finite_discrepancy_transfer]
    exact hbad
  obtain ⟨v, hv, hvA, hcoeff⟩ := hinv c (fun j => roughVectorMvProjection_degree _ hp) N hN F' hF' hbad'
  let χ := nativeHorizontalTorusFunctional (I := D.I) D.Γ v
  refine ⟨χ, native_horizontal_torus_functional_horizontal (I := D.I) D.Γ v hv, ?_, ?_⟩
  · exact (native_horizontal_torus_functional_norm (I := D.I) D.Γ v).trans
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hvA)
        (rough_basis_operator_norm_budget_positive _).le)
  · intro J hJ
    change (N : ℝ)^(∑ i, J i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J)
      (roughVectorMvProjection (nativeHorizontalTorusFunctional (I := D.I) D.Γ v).toLinearMap p) : ℝ) :
        UnitAddCircle)‖ ≤ (A : ℝ)
    rw [native_horizontal_torus_functional_polynomial]
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
    exact hcoeff J hJ

theorem native_abelian_original_polynomial_observable_inverse
    (D : NativeNilmanifoldData.{u} 1) (n d : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : MeasurableSpace (D.G ⧸ D.Γ) := borel (D.G ⧸ D.Γ)
    ∃ A : ℕ, 0 < A ∧ ∀ (Q : (Fin n → ℝ) → D.G) (p : RoughVectorMvPolynomial (Fin n) D.E),
      RoughVectorMvDegreeLE p d →
        (∀ x, nativeLieGlobalLogarithm (E := D.E) (I := D.I) (Q x) = roughVectorMvEval p x) →
        ∀ N : ℕ, 0 < N → ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
          δ ≤ ‖finiteComplexSetMean (scalarMvIntegerCube (Fin n) N)
            (fun x => F (Q (fun i => (x i : ℝ)) : D.G ⧸ D.Γ)) - ∫ q, F q ∂nativeAbelianTorusHaar D‖ →
          ∃ χ : D.E →L[ℝ] ℝ, RoughNativeHorizontalFunctional (I := D.I) D.Γ χ.toLinearMap ∧
            ‖χ‖ ≤ roughBasisOperatorNormBudget (nativeLatticeFilteredSmoothRealBasis (I := D.I) D.Γ)*(A : ℝ) ∧
            ∀ J : Fin n → ℕ, 0 < (∑ i, J i) →
              (N : ℝ)^(∑ i, J i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J)
                (roughVectorMvProjection χ.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : MeasurableSpace (D.G ⧸ D.Γ) := borel (D.G ⧸ D.Γ)
  obtain ⟨A, hA, hinv⟩ := native_abelian_mv_polynomial_observable_inverse D n d δ hδ
  refine ⟨A, hA, ?_⟩
  intro Q p hp hQ N hN F hF hbad
  have he : (fun x : Fin n → ℤ => (Q (fun i => (x i : ℝ)) : D.G ⧸ D.Γ)) =
      nativeAbelianMvPolynomialOrbit D p := by
    funext x
    unfold nativeAbelianMvPolynomialOrbit
    rw [← hQ]
    rw [nativeLieExponential_globalLogarithm]
  rw [show (fun x : Fin n → ℤ => F (Q (fun i => (x i : ℝ)) : D.G ⧸ D.Γ)) =
    (fun x => F (nativeAbelianMvPolynomialOrbit D p x)) from
      funext (fun x => congrArg F (congrFun he x))] at hbad
  exact hinv p hp N hN F hF hbad

end Hindman168
