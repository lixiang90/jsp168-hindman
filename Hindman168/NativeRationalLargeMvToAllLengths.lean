import Hindman168.NativeRationalConstantMvDiscrepancyAnchor
import Hindman168.MvBoundedLengthCoefficient
import Hindman168.NativeRationalFunctionalScalarPolynomial

/-! A TRUE large-N full inverse budget supplies ALL original positive
lengths: actual discrepancy selects a sample anchor; its constant weighted
orbit gives a genuine original character under the SAME large-N budget;
circle/degree bounds control BOTH original tables on the bounded short range.
No original character existence theorem or extra inverse is assumed. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators
universe u

theorem native_rational_large_mv_inverse_to_all_lengths {s ℓ : ℕ} {σ : Type*} [Fintype σ]
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (δ : ℝ) (Q T : ℕ) (hT : 0 < T) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    (∀ p : RoughVectorMvPolynomial σ D.E, RoughVectorMvWeightedDegree L.layer p 0 →
      ∀ N : ℕ, T ≤ N → ∀ H ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
      δ ≤ ‖nativeNilmanifoldFiniteDiscrepancy D (scalarMvIntegerCube σ N) (nativeMvPolynomialOrbit D p) H‖ →
      ∃ κ : D.E →L[ℝ] ℝ,
        RoughNativeHorizontalFunctional (I := D.I) D.Γ κ.toLinearMap ∧ ‖κ‖ ≤ (Q : ℝ) ∧
        κ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (I := D.I) D.Γ (Q : ℝ) ∧
        (∀ I : σ → ℕ, 0 < (∑ i, I i) →
          (N : ℝ)^(∑ i, I i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I)
            (roughVectorMvProjection κ.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ (Q : ℝ)) ∧
        ∀ I : σ → ℕ, 0 < (∑ i, I i) →
          (N : ℝ)^(∑ i, I i)*‖((mvPolynomialBinomialCoefficient
            (roughVectorMvProjection κ.toLinearMap p) ℓ I : ℝ) : UnitAddCircle)‖ ≤ (Q : ℝ)) →
    ∃ R : ℕ, 0 < R ∧
      ∀ p : RoughVectorMvPolynomial σ D.E, RoughVectorMvWeightedDegree L.layer p 0 →
      ∀ N : ℕ, 0 < N → ∀ H ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
      δ ≤ ‖nativeNilmanifoldFiniteDiscrepancy D (scalarMvIntegerCube σ N) (nativeMvPolynomialOrbit D p) H‖ →
      ∃ κ : D.E →L[ℝ] ℝ,
        RoughNativeHorizontalFunctional (I := D.I) D.Γ κ.toLinearMap ∧ ‖κ‖ ≤ (R : ℝ) ∧
        κ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (I := D.I) D.Γ (R : ℝ) ∧
        (∀ I : σ → ℕ, 0 < (∑ i, I i) →
          (N : ℝ)^(∑ i, I i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I)
            (roughVectorMvProjection κ.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ (R : ℝ)) ∧
        ∀ I : σ → ℕ, 0 < (∑ i, I i) →
          (N : ℝ)^(∑ i, I i)*‖((mvPolynomialBinomialCoefficient
            (roughVectorMvProjection κ.toLinearMap p) ℓ I : ℝ) : UnitAddCircle)‖ ≤ (R : ℝ) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro hLarge
  let R := Q+T^ℓ+mvBinomialCoefficientBudget σ ℓ*T^ℓ+1
  have hR : 0 < R := by dsimp only [R]; omega
  have hQR : (Q : ℝ) ≤ (R : ℝ) := by exact_mod_cast (show Q ≤ R by dsimp only [R]; omega)
  have hMonoR : ((T^ℓ : ℕ) : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast (show T^ℓ ≤ R by dsimp only [R]; omega)
  have hBinR : (mvBinomialCoefficientBudget σ ℓ : ℝ)*((T^ℓ : ℕ) : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast (show mvBinomialCoefficientBudget σ ℓ*T^ℓ ≤ R by dsimp only [R]; omega)
  refine ⟨R,hR,?_⟩
  intro p hp N hN H hH hBad
  by_cases hTN : T ≤ N
  · obtain ⟨κ,hHor,hNorm,_hGrid,hMono,hBin⟩ := hLarge p hp N hTN H hH hBad
    have hn := hNorm.trans hQR
    exact ⟨κ,hHor,hn,
      rough_native_norm_bounded_horizontal_grid_mem D.Γ (R : ℝ) (Nat.cast_nonneg R) κ hn hHor,
      fun I hI => (hMono I hI).trans hQR,fun I hI => (hBin I hI).trans hQR⟩
  · obtain ⟨v,hAnchor⟩ := native_rational_constant_mv_discrepancy_anchor D p N hN δ H hBad
    obtain ⟨κ,hHor,hNorm,_hGrid,_hConstMono,_hConstBin⟩ :=
      hLarge (nativeRationalConstantMvPolynomial σ D v) (native_rational_constant_mv_polynomial_weighted D L v)
        T le_rfl H hH (hAnchor T hT)
    have hKill : L.layer (ℓ+1) ≤ κ.toLinearMap.ker := by rw [L.terminal]; exact bot_le
    have hDegree := native_rational_functional_scalar_degree D L p hp κ ℓ hKill
    have hMono := mv_bounded_length_coefficient (roughVectorMvProjection κ.toLinearMap p) ℓ N T
      hDegree hN (Nat.le_of_lt (Nat.lt_of_not_ge hTN))
    have hBin := mv_complete_binomial_transfer _ ℓ N ((T^ℓ : ℕ) : ℝ) hN (Nat.cast_nonneg _) hMono
    have hn := hNorm.trans hQR
    exact ⟨κ,hHor,hn,
      rough_native_norm_bounded_horizontal_grid_mem D.Γ (R : ℝ) (Nat.cast_nonneg R) κ hn hHor,
      fun I hI => (hMono I hI).trans hMonoR,fun I hI => (hBin I hI).trans hBinR⟩

end Hindman168
