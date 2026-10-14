import Hindman168.NativeRationalCompactUnivariateScalars
import Hindman168.NativeRationalDenseRelativeCharacter
import Hindman168.ScalarDenseDifferenceBinomialSeparation

/-! Actual common relative character yields ONE bounded common multiplier
for BOTH higher nonlinear coefficient tables at the original N scale.
All constants/grids/large-N thresholds precede original raw coefficients. -/
namespace Hindman168
open MeasureTheory Polynomial
open scoped Manifold ContDiff BigOperators
universe u

theorem native_rational_dense_nonlinear_separation {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (hdeg : 2 ≤ ℓ)
    (hInverse : NativeRationalWeightedInverseStatement (nativeRationalDegreeReducedData D L)
      (nativeDegreeReducedRationalLieFiltration D L) Unit)
    (k : nativeRationalTerminalIndex D L → ℤ) (hk : k ≠ 0)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    letI : MeasurableSpace (nativeRationalRelativeData D L 1).E := borel (nativeRationalRelativeData D L 1).E
    letI : MeasurableSpace (nativeRationalRelativeData D L 1).G := borel (nativeRationalRelativeData D L 1).G
    letI : MeasurableSpace (nativeRationalDegreeReducedData D L).E := borel (nativeRationalDegreeReducedData D L).E
    letI : MeasurableSpace (nativeRationalDegreeReducedData D L).G := borel (nativeRationalDegreeReducedData D L).G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ A B ρ : ℝ, ∃ S T : ℕ, 0 < A ∧ 0 < B ∧ 0 < ρ ∧ 0 < S ∧ 0 < T ∧
      ∃ C : Finset ((nativeRationalRelativeData D L 1).E →L[ℝ] ℝ),
      ∀ (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
        (N : ℕ), T ≤ N → ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
        4 ≤ δ^2*(N : ℝ) →
        δ ≤ ‖finiteComplexSetMean (Finset.Ico 0 (N : ℤ)) (fun n =>
          nativeRationalTerminalFourierProjection D L k F (nativeMvPolynomialOrbit D p (fun _ => n)))‖ →
        ∃ χ ∈ C,
          RoughNativeHorizontalFunctional (I := (nativeRationalRelativeData D L 1).I)
            (nativeRationalRelativeData D L 1).Γ χ.toLinearMap ∧ ‖χ‖ ≤ A ∧
          ∃ M : ℕ, 0 < M ∧ M ≤ S ∧
            (∀ j : ℕ, 3 ≤ j → j ≤ ℓ → (N : ℝ)^j*
              ‖(((M : ℝ)*(nativeRationalCompactNonlinearScalar D L p hp χ).coeff j : ℝ) : UnitAddCircle)‖ ≤ B) ∧
            (∀ j : ℕ, 3 ≤ j → j ≤ ℓ → (N : ℝ)^j*
              ‖(((M : ℝ)*scalarPolynomialBinomialCoefficient
                (nativeRationalCompactNonlinearScalar D L p hp χ) ℓ j : ℝ) : UnitAddCircle)‖ ≤ B) ∧
            ∃ U : Finset ℕ, U.Nonempty ∧ ρ*(N : ℝ) ≤ U.card ∧
              ∀ h ∈ U, 0 < h ∧ h < N ∧ NativeRationalRelativeCoefficientBounds D L p hp h χ N B := by
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).E := borel (nativeRationalRelativeData D L 1).E
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).G := borel (nativeRationalRelativeData D L 1).G
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).E := borel (nativeRationalDegreeReducedData D L).E
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).G := borel (nativeRationalDegreeReducedData D L).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨A,R,ρ,hA,hR,hρ,C,hDense⟩ := native_rational_dense_relative_character D L hdeg hInverse k hk δ hδ hδ1
  let μ : ℝ := min ρ 1
  have hμ : 0 < μ := lt_min hρ zero_lt_one
  have hμ1 : μ ≤ 1 := min_le_right _ _
  obtain ⟨S,T,B,hS,hT,hB,hSep⟩ := scalar_dense_difference_binomial_separation ℓ μ R hμ hμ1 hR.le
  let K : ℝ := B+R+1
  have hBK : B ≤ K := by dsimp [K]; linarith
  have hRK : R ≤ K := by dsimp [K]; linarith
  refine ⟨A,K,ρ,S,T,hA,by dsimp [K]; positivity,hρ,hS,hT,C,?_⟩
  intro p hp N hTN F hF hlarge hmean
  have hN : 0 < N := hT.trans_le hTN
  obtain ⟨χ,hχ,hHor,hNorm,U,hUne,hsize,hUseful⟩ := hDense p hp N hN F hF hlarge hmean
  have hU : U ⊆ Finset.range N := fun h hh => Finset.mem_range.mpr (hUseful h hh).2.1
  have hsizeμ : μ*(N : ℝ) ≤ U.card :=
    (mul_le_mul_of_nonneg_right (min_le_left ρ 1) (Nat.cast_nonneg N)).trans hsize
  have hSecond : ∀ h ∈ U, (N : ℝ)^2*
      ‖((scalarDifferencePolynomial (nativeRationalCompactDiagonalScalar D L p χ)
        (nativeRationalCompactNonlinearScalar D L p hp χ) h (nativeRationalCompactCommutatorSlope D L p χ h)).coeff 2 :
          UnitAddCircle)‖ ≤ R := by
    intro h hh
    exact native_rational_compact_univariate_second_bound D L hdeg p hp χ hHor.2.1 h N R
      (hUseful h hh).2.2.2
  obtain ⟨M,hM,hMS,hMon,hBin⟩ := hSep (nativeRationalCompactDiagonalScalar D L p χ)
    (nativeRationalCompactNonlinearScalar D L p hp χ)
    (native_rational_compact_nonlinear_scalar_degree D L p hp χ)
    (nativeRationalCompactCommutatorSlope D L p χ) N hTN U hU hsizeμ hSecond
  refine ⟨χ,hχ,hHor,hNorm,M,hM,hMS,fun j hj hjL => (hMon j hj hjL).trans hBK,
    fun j hj hjL => (hBin j hj hjL).trans hBK,U,hUne,hsize,?_⟩
  intro h hh
  obtain ⟨hpos,hlt,_,hBounds⟩ := hUseful h hh
  exact ⟨hpos,hlt,⟨fun J hJ hjL => (hBounds.1 J hJ hjL).trans hRK,
    fun J hJ hjL => (hBounds.2 J hJ hjL).trans hRK⟩⟩

end Hindman168
