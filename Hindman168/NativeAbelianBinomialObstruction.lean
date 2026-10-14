import Hindman168.NativeAbelianMvPolynomialInverse
import Hindman168.MvBinomialCoefficientModOne

/-! The corrected equal-cube input for the ORIGINAL abelian nilmanifold,
in the actual paper binomial basis and one fixed finite native character grid. -/

namespace Hindman168
open MeasureTheory Module
open scoped Classical BigOperators Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_original_character_binomial_expansion {σ : Type*} [Fintype σ]
    {s : ℕ} (D : NativeNilmanifoldData.{u} s) (Q : (σ → ℝ) → D.G)
    (p : RoughVectorMvPolynomial σ D.E) (d : ℕ) (hp : RoughVectorMvDegreeLE p d)
    (hQ : ∀ x, nativeLieGlobalLogarithm (E := D.E) (I := D.I) (Q x) = roughVectorMvEval p x)
    (χ : D.E →ₗ[ℝ] ℝ) (x : σ → ℝ) :
    nativeLieLogarithmCharacter (I := D.I) (G := D.G) χ (Q x) =
      MvPolynomial.eval x (MvPolynomial.C (mvPolynomialBinomialCoefficient (roughVectorMvProjection χ p) d 0)+
        ∑ J ∈ roughSpatialDegreeIndices σ d,
          MvPolynomial.C (mvPolynomialBinomialCoefficient (roughVectorMvProjection χ p) d J)*
            roughMvBinomialPolynomial J) := by
  rw [← mv_polynomial_binomial_positive_expansion (roughVectorMvProjection χ p) d
    (roughVectorMvProjection_degree χ hp), roughVectorMvProjection_eval]
  change χ (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (Q x)) = _
  rw [hQ]

theorem native_abelian_binomial_observable_obstruction
    (D : NativeNilmanifoldData.{u} 1) (n d : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : MeasurableSpace (D.G ⧸ D.Γ) := borel (D.G ⧸ D.Γ)
    ∃ M : ℕ, 0 < M ∧ ∀ (Q : (Fin n → ℝ) → D.G) (p : RoughVectorMvPolynomial (Fin n) D.E),
      RoughVectorMvDegreeLE p d →
        (∀ x, nativeLieGlobalLogarithm (E := D.E) (I := D.I) (Q x) = roughVectorMvEval p x) →
        ∀ N : ℕ, 0 < N → ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
          δ ≤ ‖finiteComplexSetMean (scalarMvIntegerCube (Fin n) N)
            (fun x => F (Q (fun i => (x i : ℝ)) : D.G ⧸ D.Γ)) - ∫ q, F q ∂nativeAbelianTorusHaar D‖ →
          ∃ χ : D.E →L[ℝ] ℝ,
            RoughNativeHorizontalFunctional (I := D.I) D.Γ χ.toLinearMap ∧ ‖χ‖ ≤ (M : ℝ) ∧
            χ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (I := D.I) D.Γ (M : ℝ) ∧
            (∀ J : Fin n → ℕ, 0 < (∑ i, J i) →
              (N : ℝ)^(∑ i, J i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J)
                (roughVectorMvProjection χ.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ (M : ℝ)) ∧
            ∀ J : Fin n → ℕ, 0 < (∑ i, J i) →
              (N : ℝ)^(∑ i, J i)*‖((mvPolynomialBinomialCoefficient
                (roughVectorMvProjection χ.toLinearMap p) d J : ℝ) : UnitAddCircle)‖ ≤ (M : ℝ) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : MeasurableSpace (D.G ⧸ D.Γ) := borel (D.G ⧸ D.Γ)
  obtain ⟨A, hA, hinv⟩ := native_abelian_original_polynomial_observable_inverse D n d δ hδ
  let B := ⌈roughBasisOperatorNormBudget (nativeLatticeFilteredSmoothRealBasis (I := D.I) D.Γ)⌉₊
  let T := mvBinomialCoefficientBudget (Fin n) d
  let M := (B+T+1)*A
  have hM : 0 < M := Nat.mul_pos (by dsimp only [B, T]; omega) hA
  have hAM : A ≤ M := Nat.le_mul_of_pos_left A (by omega : 0 < B+T+1)
  have hBM : B*A ≤ M := Nat.mul_le_mul_right A (by omega)
  have hTM : T*A ≤ M := Nat.mul_le_mul_right A (by omega)
  have hB : roughBasisOperatorNormBudget (nativeLatticeFilteredSmoothRealBasis (I := D.I) D.Γ) ≤ (B : ℝ) :=
    Nat.le_ceil _
  refine ⟨M, hM, ?_⟩
  intro Q p hp hQ N hN F hF hbad
  obtain ⟨χ, hχ, hnorm, hcoeff⟩ := hinv Q p hp hQ N hN F hF hbad
  have hnormM : ‖χ‖ ≤ (M : ℝ) := hnorm.trans
    ((mul_le_mul_of_nonneg_right hB (Nat.cast_nonneg A)).trans (by exact_mod_cast hBM))
  refine ⟨χ, hχ, hnormM, rough_native_norm_bounded_horizontal_grid_mem (I := D.I) D.Γ
    (M : ℝ) (Nat.cast_nonneg M) χ hnormM hχ, ?_, ?_⟩
  · exact fun J hJ => (hcoeff J hJ).trans (by exact_mod_cast hAM)
  · intro J hJ
    by_cases hJd : (∑ i, J i) ≤ d
    · have h := mv_binomial_coefficient_mod_one (roughVectorMvProjection χ.toLinearMap p)
        d 1 1 J (mv_binomial_box_mem_of_weight_le d J hJd) hJ
        (N : ℝ) (A : ℝ) (by exact_mod_cast hN) (Nat.cast_nonneg A)
        (fun I _ hI => by simpa only [Nat.cast_one, one_mul] using hcoeff I hI)
      simpa only [Nat.cast_one, one_mul] using h.trans (by exact_mod_cast hTM)
    · rw [mv_binomial_coefficient_zero_above_degree _ d
        (roughVectorMvProjection_degree χ.toLinearMap hp) J (Nat.lt_of_not_ge hJd),
        AddCircle.coe_zero, norm_zero, mul_zero]
      exact Nat.cast_nonneg M

end Hindman168
