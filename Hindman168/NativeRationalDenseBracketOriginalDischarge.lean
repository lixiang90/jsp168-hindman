import Hindman168.NativeRationalDenseBracketFullAlternative
import Hindman168.NativeRationalFirstLayerInverseReconstruction

/-! GENUINE FULL fixed-data Claim 7.7 alternative from SAME original Fourier
signal, preserving relative character, common natural M, BOTH higher P/Q
tables and geometry-only budgets before all raw sources. Original inverse
case-(i) character/reducible-filtration reconstruction remains open. -/
namespace Hindman168
open MeasureTheory Polynomial
open scoped Manifold ContDiff BigOperators
universe u

theorem native_rational_dense_bracket_original_discharge {s ℓ : ℕ}
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
    ∃ A Q S T : ℕ, 0 < A ∧ 0 < Q ∧ 0 < S ∧ 0 < T ∧
      ∃ C : Finset ((nativeRationalRelativeData D L 1).E →L[ℝ] ℝ),
      ∀ (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
        (N : ℕ), T ≤ N → ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
        4 ≤ δ^2*(N : ℝ) →
        δ ≤ ‖finiteComplexSetMean (Finset.Ico 0 (N : ℤ)) (fun n =>
          nativeRationalTerminalFourierProjection D L k F (nativeMvPolynomialOrbit D p (fun _ => n)))‖ →
        (∃ χ : D.E →L[ℝ] ℝ, RoughNativeHorizontalFunctional (I := D.I) D.Γ χ.toLinearMap ∧
            ‖χ‖ ≤ (Q : ℝ) ∧ χ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (I := D.I) D.Γ (Q : ℝ) ∧
            (∀ J : Unit → ℕ, 0 < (∑ i, J i) →
              (N : ℝ)^(∑ i, J i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J)
                (roughVectorMvProjection χ.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ (Q : ℝ)) ∧
            ∀ J : Unit → ℕ, 0 < (∑ i, J i) →
              (N : ℝ)^(∑ i, J i)*‖((mvPolynomialBinomialCoefficient
                (roughVectorMvProjection χ.toLinearMap p) ℓ J : ℝ) : UnitAddCircle)‖ ≤ (Q : ℝ)) ∨
        (∃ χ ∈ C,
          RoughNativeHorizontalFunctional (I := (nativeRationalRelativeData D L 1).I)
            (nativeRationalRelativeData D L 1).Γ χ.toLinearMap ∧ ‖χ‖ ≤ (A : ℝ) ∧
          ∃ M : ℕ, 0 < M ∧ M ≤ S ∧
            (∀ j : ℕ, 3 ≤ j → j ≤ ℓ → (N : ℝ)^j*
              ‖(((M : ℝ)*(nativeRationalCompactNonlinearScalar D L p hp χ).coeff j : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)) ∧
            (∀ j : ℕ, 3 ≤ j → j ≤ ℓ → (N : ℝ)^j*
              ‖(((M : ℝ)*scalarPolynomialBinomialCoefficient
                (nativeRationalCompactNonlinearScalar D L p hp χ) ℓ j : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)) ∧
            (∀ j : ℕ, 2 ≤ j → j ≤ ℓ → (N : ℝ)^j*
              ‖(((M : ℝ)*(nativeRationalCompactDiagonalScalar D L p χ).coeff j : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)) ∧
            (∀ j : ℕ, 2 ≤ j → j ≤ ℓ → (N : ℝ)^j*
              ‖(((M : ℝ)*scalarPolynomialBinomialCoefficient
                (nativeRationalCompactDiagonalScalar D L p χ) ℓ j : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)) ∧
            ∃ b : NativeRationalFirstLayerIndex D L → ℤ,
              (∀ i, |(b i : ℝ)| ≤ (A : ℝ)) ∧
              ∃ r : ℕ, 0 < r ∧ r ≤ A ∧ ∀ i,
                (N : ℝ)*‖(((r : ℝ)*nativeRationalCompactBracketCoefficient D L p χ M i : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)) := by
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).E := borel (nativeRationalRelativeData D L 1).E
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).G := borel (nativeRationalRelativeData D L 1).G
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).E := borel (nativeRationalDegreeReducedData D L).E
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).G := borel (nativeRationalDegreeReducedData D L).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨A,S,T,hA,hS,hT,C,hfull⟩ :=
    native_rational_dense_bracket_full_alternative D L hdeg hInverse k hk δ hδ hδ1
  obtain ⟨Q,hQ,hreconstruct⟩ := native_rational_first_layer_inverse_reconstruction D L
    (A : ℝ) (A : ℝ) (Nat.cast_nonneg A) (Nat.cast_nonneg A)
  refine ⟨A,Q,S,T,hA,hQ,hS,hT,C,?_⟩
  intro p hp N hTN F hF hlarge hmean
  obtain ⟨χ,hχ,hhor,hnorm,M,hM,hMS,hQM,hQB,hPM,hPB,b,hb,halt⟩ :=
    hfull p hp N hTN F hF hlarge hmean
  rcases halt with hcoeff | hvector
  · exact Or.inr ⟨χ,hχ,hhor,hnorm,M,hM,hMS,hQM,hQB,hPM,hPB,b,hb,hcoeff⟩
  · obtain ⟨v,hv,hsize,hphase⟩ := hvector
    have hvi : ∀ i, |(v i : ℝ)| ≤ (A : ℝ) := by
      intro i
      have hn := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hsize
      have hr : ((v i).natAbs : ℝ) ≤ A := by exact_mod_cast hn
      simpa only [Nat.cast_natAbs,Int.cast_abs] using hr
    exact Or.inl (hreconstruct p hp N (hT.trans_le hTN) v hv hvi hphase)

end Hindman168
