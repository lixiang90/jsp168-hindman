import Hindman168.NativeRationalLayerLogPolynomial
import Hindman168.NativeOriginalPolynomialInverse

/-! The ordinary native inverse on the actual rational subgroup gives an
original rational level character and bounds for the COMPLETE original
scalar polynomial. The finite grid and bound precede every source input. -/
namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_layer_polynomial_inverse {s ℓ : ℕ} {σ : Type*} [Fintype σ]
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (δ : ℝ) (hδ : 0 < δ) :
    let A := nativeRationalLayerOrbitData D F 0 rho hRat
    letI : MeasurableSpace A.E := borel A.E
    letI : MeasurableSpace A.G := borel A.G
    letI := A.metric
    letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
    ∃ M : ℕ, 0 < M ∧
      ∀ (p : RoughVectorMvPolynomial σ D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0),
      ∀ N : ℕ, 0 < N → ∀ f ∈ unitLipschitzObservables (A.G ⧸ A.Γ),
      δ ≤ ‖finiteComplexSetMean (scalarMvIntegerCube σ N)
        (fun x => f (QuotientGroup.mk (s := A.Γ) (show A.G from
          nativeRationalSubgroupPolynomialOrbit D F p hp (fun i => (x i : ℝ))))) -
          ∫ q, f q ∂nativeNilmanifoldQuotientProbability A‖ →
      ∃ chi : A.E →ₗ[ℝ] ℝ,
        chi ∈ roughNativeHorizontalCharacterGrid (I := A.I) A.Γ (M : ℝ) ∧
        ∃ j : ℕ, 1 ≤ j ∧ j ≤ ℓ ∧
          NativeSubgroupRationalLevelCharacter D F j
            (nativeSubgroupHorizontalExtension D F rho hRat chi) ∧
          (∀ k : ℕ, j < k → F.layer k ≤
            (nativeSubgroupHorizontalExtension D F rho hRat chi).ker) ∧
          (∀ J : σ → ℕ, 0 < (∑ i, J i) →
            (N : ℝ)^(∑ i, J i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J)
              (roughVectorMvProjection (nativeSubgroupHorizontalExtension D F rho hRat chi) p) : ℝ) :
                UnitAddCircle)‖ ≤ (M : ℝ)) ∧
          ∀ J : σ → ℕ, 0 < (∑ i, J i) →
            (N : ℝ)^(∑ i, J i)*‖((mvPolynomialBinomialCoefficient
              (roughVectorMvProjection (nativeSubgroupHorizontalExtension D F rho hRat chi) p) ℓ J : ℝ) :
                UnitAddCircle)‖ ≤ (M : ℝ) := by
  let A := nativeRationalLayerOrbitData D F 0 rho hRat
  letI : MeasurableSpace A.E := borel A.E
  letI : MeasurableSpace A.G := borel A.G
  letI := A.metric
  letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨M,hM,hInv⟩ := native_original_polynomial_observable_inverse (σ := σ) A ℓ δ hδ
  refine ⟨M,hM,?_⟩
  intro p hp N hN f hf hBad
  obtain ⟨chi,hHor,_hNorm,hGrid,hMono,hBin⟩ := hInv
    (nativeRationalSubgroupPolynomialOrbit D F p hp) (nativeRationalLayerLogPolynomial D F p)
    (native_rational_layer_log_polynomial_degree D F p hp)
    (native_rational_layer_log_polynomial_log D F rho hRat p hp) N hN f hf hBad
  obtain ⟨j,hj,hjTop,hLevel,hTail⟩ :=
    native_actual_subgroup_horizontal_maximal_level D F rho hRat chi.toLinearMap hHor
  rw [native_rational_layer_log_polynomial_projection D F rho hRat p chi.toLinearMap] at hMono hBin
  exact ⟨chi.toLinearMap,hGrid,j,hj,hjTop,hLevel,hTail,hMono,hBin⟩

end Hindman168
