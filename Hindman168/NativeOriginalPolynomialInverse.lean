import Hindman168.NativeRationalFiniteVariablesInverse
import Hindman168.MvCompleteBinomialTransfer

/-! UNCONDITIONAL actual ORIGINAL logarithmic-polynomial equal-cube inverse
at every native step bound and ordinary degree, including degree zero.
True stretched weights supply the inverse input; both COMPLETE output tables
use the original ordinary degree, original character and canonical Haar. -/
namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_original_polynomial_observable_inverse {s : ℕ} {σ : Type*} [Fintype σ]
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ M : ℕ, 0 < M ∧ ∀ (Q : (σ → ℝ) → D.G) (p : RoughVectorMvPolynomial σ D.E),
      RoughVectorMvDegreeLE p d →
      (∀ x, nativeLieGlobalLogarithm (E := D.E) (I := D.I) (Q x) = roughVectorMvEval p x) →
      ∀ N : ℕ, 0 < N → ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
      δ ≤ ‖finiteComplexSetMean (scalarMvIntegerCube σ N)
        (fun x => F (Q (fun i => (x i : ℝ)) : D.G ⧸ D.Γ)) -
          ∫ q, F q ∂nativeNilmanifoldQuotientProbability D‖ →
      ∃ χ : D.E →L[ℝ] ℝ,
        RoughNativeHorizontalFunctional (I := D.I) D.Γ χ.toLinearMap ∧ ‖χ‖ ≤ (M : ℝ) ∧
        χ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (I := D.I) D.Γ (M : ℝ) ∧
        (∀ J : σ → ℕ, 0 < (∑ i, J i) →
          (N : ℝ)^(∑ i, J i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J)
            (roughVectorMvProjection χ.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ (M : ℝ)) ∧
        ∀ J : σ → ℕ, 0 < (∑ i, J i) →
          (N : ℝ)^(∑ i, J i)*‖((mvPolynomialBinomialCoefficient
            (roughVectorMvProjection χ.toLinearMap p) d J : ℝ) : UnitAddCircle)‖ ≤ (M : ℝ) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  let e := max d 1
  have he : 0 < e := zero_lt_one.trans_le (le_max_right _ _)
  let L := nativeOriginalRationalLieFiltration D e he
  obtain ⟨A,hA,hInv⟩ := native_rational_weighted_inverse_finite_variables D L σ δ hδ
  let T := mvBinomialCoefficientBudget σ d
  let M := (T+1)*A
  have hM : 0 < M := Nat.mul_pos (by omega) hA
  have hAM : A ≤ M := Nat.le_mul_of_pos_left A (by omega : 0 < T+1)
  have hTM : T*A ≤ M := Nat.mul_le_mul_right A (by omega)
  have hAR : (A : ℝ) ≤ M := by exact_mod_cast hAM
  have hTR : (T : ℝ)*(A : ℝ) ≤ M := by exact_mod_cast hTM
  refine ⟨M,hM,?_⟩
  intro Q p hp hQ N hN F hF hBad
  have hWeight : RoughVectorMvWeightedDegree L.layer p 0 :=
    rough_native_weighted_polynomial_initial e he (fun a ha => (hp a ha).trans (le_max_left _ _))
  have hOrbit (x : σ → ℤ) : (Q (fun j => (x j : ℝ)) : D.G ⧸ D.Γ) = nativeMvPolynomialOrbit D p x := by
    unfold nativeMvPolynomialOrbit
    rw [← hQ,nativeLieExponential_globalLogarithm]
  have hBad' : δ ≤ ‖nativeNilmanifoldFiniteDiscrepancy D (scalarMvIntegerCube σ N)
      (nativeMvPolynomialOrbit D p) F‖ := by
    change δ ≤ ‖finiteComplexSetMean _ (fun x => F (nativeMvPolynomialOrbit D p x)) - _‖
    simpa only [hOrbit] using hBad
  obtain ⟨χ,hHor,hNorm,_hGrid,hMono,_hBin⟩ := hInv p hWeight N hN F hF hBad'
  have hn := hNorm.trans hAR
  have hBin := mv_complete_binomial_transfer (roughVectorMvProjection χ.toLinearMap p) d N
    (A : ℝ) hN (Nat.cast_nonneg A) hMono
  exact ⟨χ,hHor,hn,rough_native_norm_bounded_horizontal_grid_mem D.Γ (M : ℝ)
    (Nat.cast_nonneg M) χ hn hHor,
    fun J hJ => (hMono J hJ).trans hAR,fun J hJ => (hBin J hJ).trans hTR⟩

end Hindman168
