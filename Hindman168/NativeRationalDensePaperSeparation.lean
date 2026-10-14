import Hindman168.NativeRationalDenseNonlinearSeparation
import Hindman168.NativeRationalCompactDiagonalScalarGeometry
import Hindman168.ScalarDifferenceFullSeparation

/-! COMPLETE actual paper scalar separation on SAME native useful shifts:
both higher P/Q tables and beta+alpha*h+sigma(h) at original N scale.
Original horizontal reconstruction/bracket alternative remain open. -/
namespace Hindman168
open MeasureTheory Polynomial
open scoped Manifold ContDiff BigOperators
universe u

theorem native_rational_dense_paper_separation {s ℓ : ℕ}
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
            (∀ j : ℕ, 2 ≤ j → j ≤ ℓ → (N : ℝ)^j*
              ‖(((M : ℝ)*(nativeRationalCompactDiagonalScalar D L p χ).coeff j : ℝ) : UnitAddCircle)‖ ≤ B) ∧
            (∀ j : ℕ, 2 ≤ j → j ≤ ℓ → (N : ℝ)^j*
              ‖(((M : ℝ)*scalarPolynomialBinomialCoefficient
                (nativeRationalCompactDiagonalScalar D L p χ) ℓ j : ℝ) : UnitAddCircle)‖ ≤ B) ∧
            ∃ U : Finset ℕ, U.Nonempty ∧ ρ*(N : ℝ) ≤ U.card ∧
              ∀ h ∈ U, 0 < h ∧ h < N ∧ NativeRationalRelativeCoefficientBounds D L p hp h χ N B ∧
                (N : ℝ)*‖(((M : ℝ)*((nativeRationalCompactDiagonalScalar D L p χ).eval 1+
                  scalarPolynomialBinomialCoefficient (nativeRationalCompactNonlinearScalar D L p hp χ) ℓ 2*(h : ℝ)+
                  nativeRationalCompactCommutatorSlope D L p χ h) : ℝ) : UnitAddCircle)‖ ≤ B := by
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).E := borel (nativeRationalRelativeData D L 1).E
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).G := borel (nativeRationalRelativeData D L 1).G
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).E := borel (nativeRationalDegreeReducedData D L).E
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).G := borel (nativeRationalDegreeReducedData D L).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨A,B,ρ,S,T,hA,hB,hρ,hS,hT,C,hData⟩ := native_rational_dense_nonlinear_separation D L hdeg hInverse k hk δ hδ hδ1
  let CP : ℝ := (S : ℝ)*B+(scalarTaylorTailBudget ℓ : ℝ)*B
  let CB : ℝ := (scalarBinomialCoefficientBudget ℓ : ℝ)*CP
  let CL : ℝ := CP+(ℓ+1 : ℕ)*CP+(scalarBinomialCoefficientBudget ℓ : ℝ)*B
  let K : ℝ := B+CP+CB+CL+1
  have hCP : 0 ≤ CP := by dsimp [CP]; positivity
  have hCB : 0 ≤ CB := by dsimp [CB]; positivity
  have hCL : 0 ≤ CL := by dsimp [CL]; positivity
  have hBK : B ≤ K := by dsimp [K]; linarith
  have hCPK : CP ≤ K := by dsimp [K]; linarith
  have hCBK : CB ≤ K := by dsimp [K]; linarith
  have hCLK : CL ≤ K := by dsimp [K]; linarith
  refine ⟨A,K,ρ,S,T,hA,by dsimp [K]; positivity,hρ,hS,hT,C,?_⟩
  intro p hp N hTN F hF hlarge hmean
  have hN : 0 < N := hT.trans_le hTN
  obtain ⟨χ,hχ,hHor,hNorm,M,hM,hMS,hQM,hQB,U,hUne,hsize,hUseful⟩ := hData p hp N hTN F hF hlarge hmean
  have hCombined : ∀ h ∈ U, ∀ i : ℕ, 0 < i → i ≤ ℓ →
      (N : ℝ)^i*‖((scalarDifferencePolynomial (nativeRationalCompactDiagonalScalar D L p χ)
        (nativeRationalCompactNonlinearScalar D L p hp χ) h (nativeRationalCompactCommutatorSlope D L p χ h)).coeff i :
          UnitAddCircle)‖ ≤ B := by
    intro h hh i hi hiL
    exact native_rational_compact_univariate_coefficient_bound D L p hp χ hHor.2.1 h N i B hi hiL
      (hUseful h hh).2.2
  obtain ⟨hPM,hPB,hLinear⟩ := scalar_difference_full_separation (nativeRationalCompactDiagonalScalar D L p χ)
    (nativeRationalCompactNonlinearScalar D L p hp χ) ℓ M S N B B
    (native_rational_compact_diagonal_scalar_degree D L p hp χ)
    (native_rational_compact_nonlinear_scalar_degree D L p hp χ) hdeg
    (native_rational_compact_diagonal_scalar_zero D L p χ) hMS hN hB.le hB.le
    (nativeRationalCompactCommutatorSlope D L p χ) U hUne
    (fun h hh => (hUseful h hh).2.1.le) hCombined hQM
  refine ⟨χ,hχ,hHor,hNorm,M,hM,hMS,fun j hj hjL => (hQM j hj hjL).trans hBK,
    fun j hj hjL => (hQB j hj hjL).trans hBK,fun j hj hjL => (hPM j hj hjL).trans hCPK,
    fun j hj hjL => (hPB j hj hjL).trans hCBK,U,hUne,hsize,?_⟩
  intro h hh
  obtain ⟨hpos,hlt,hBounds⟩ := hUseful h hh
  exact ⟨hpos,hlt,⟨fun J hJ hjL => (hBounds.1 J hJ hjL).trans hBK,
    fun J hJ hjL => (hBounds.2 J hJ hjL).trans hBK⟩,(hLinear h hh).trans hCLK⟩

end Hindman168
