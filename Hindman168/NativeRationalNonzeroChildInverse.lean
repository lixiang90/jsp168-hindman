import Hindman168.NativeRationalCompactTerminalPairUnitDetection
import Hindman168.NativeRationalWeightedInverseStatement
import Hindman168.NativeUnitCubePolynomialDiscrepancy

/-! Genuine nonzero-mode inverse extraction on the actual constructed child.
The sole inverse premise is the full lower-degree inverse on this actual datum.
This does not yet reconstruct an original nonzero horizontal character. -/
namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff BigOperators
universe u

theorem native_rational_nonzero_child_inverse {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (hdeg : 2 ≤ ℓ)
    (hInverse : NativeRationalWeightedInverseStatement (nativeRationalDegreeReducedData D L)
      (nativeDegreeReducedRationalLieFiltration D L) Unit)
    (k : nativeRationalTerminalIndex D L → ℤ) (hk : k ≠ 0) (η : ℝ) (hη : 0 < η) :
    letI : MeasurableSpace (nativeRationalRelativeData D L 1).E := borel (nativeRationalRelativeData D L 1).E
    letI : MeasurableSpace (nativeRationalRelativeData D L 1).G := borel (nativeRationalRelativeData D L 1).G
    letI : MeasurableSpace (nativeRationalDegreeReducedData D L).E := borel (nativeRationalDegreeReducedData D L).E
    letI : MeasurableSpace (nativeRationalDegreeReducedData D L).G := borel (nativeRationalDegreeReducedData D L).G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ M : ℕ, 0 < M ∧
      ∀ (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
        (h : ℤ) (N : ℕ), 0 < N → ∀ H ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
        η ≤ ‖finiteComplexSetMean (Finset.Ico 0 (N : ℤ)) (fun n =>
          nativeRationalTerminalFourierProjection D L k H (nativeMvPolynomialOrbit D p (fun _ => n+h)) *
            star (nativeRationalTerminalFourierProjection D L k H (nativeMvPolynomialOrbit D p (fun _ => n))))‖ →
        ∃ χ : (nativeRationalDegreeReducedData D L).E →L[ℝ] ℝ,
          RoughNativeHorizontalFunctional (I := (nativeRationalDegreeReducedData D L).I)
            (nativeRationalDegreeReducedData D L).Γ χ.toLinearMap ∧ ‖χ‖ ≤ (M : ℝ) ∧
          χ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (I := (nativeRationalDegreeReducedData D L).I)
            (nativeRationalDegreeReducedData D L).Γ (M : ℝ) ∧
          (∀ J : Unit → ℕ, 0 < (∑ i, J i) →
            (N : ℝ)^(∑ i, J i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J)
              (roughVectorMvProjection χ.toLinearMap (nativeRationalCompactReducedPolynomial D L p hp h)) : ℝ) :
                UnitAddCircle)‖ ≤ (M : ℝ)) ∧
          ∀ J : Unit → ℕ, 0 < (∑ i, J i) →
            (N : ℝ)^(∑ i, J i)*‖((mvPolynomialBinomialCoefficient
              (roughVectorMvProjection χ.toLinearMap (nativeRationalCompactReducedPolynomial D L p hp h))
                (ℓ-1) J : ℝ) : UnitAddCircle)‖ ≤ (M : ℝ) := by
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).E := borel (nativeRationalRelativeData D L 1).E
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).G := borel (nativeRationalRelativeData D L 1).G
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).E := borel (nativeRationalDegreeReducedData D L).E
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).G := borel (nativeRationalDegreeReducedData D L).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRationalDegreeReducedData D L).metric
  letI : TopologicalSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
    (nativeRationalDegreeReducedData D L).metric.toUniformSpace.toTopologicalSpace
  obtain ⟨θ,hθ,P,hP,hDetect⟩ := native_rational_compact_terminal_pair_unit_detection D L hdeg k hk η hη
  obtain ⟨M,hM,hChild⟩ := hInverse θ hθ
  refine ⟨M,hM,?_⟩
  intro p hp h N hN H hH hLarge
  obtain ⟨J,hJ,hBad⟩ := hDetect p hp h (Finset.Ico 0 (N : ℤ)) H hH hLarge
  have hCube : θ ≤ ‖nativeNilmanifoldFiniteDiscrepancy (nativeRationalDegreeReducedData D L)
      (scalarMvIntegerCube Unit N)
      (nativeMvPolynomialOrbit (nativeRationalDegreeReducedData D L) (nativeRationalCompactReducedPolynomial D L p hp h)) J‖ := by
    rw [native_unit_cube_polynomial_discrepancy]
    exact hBad.le
  exact hChild _ (native_rational_compact_reduced_polynomial_weighted D L p hp h) N hN J (hP J hJ) hCube

end Hindman168
