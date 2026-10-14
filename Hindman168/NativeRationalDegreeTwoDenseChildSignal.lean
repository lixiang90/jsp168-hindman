import Hindman168.NativeRationalDenseChildSignal

/-! SAME original Fourier signal now yields FULL original inverse OR
GENUINE constructed smaller-source child UNIT discrepancy with UNIFORM
finite-character geometry/budgets and original-scale length. ALL previous
right-factor/dense/table data are retained. No child inverse is assumed. -/
namespace Hindman168
open MeasureTheory Polynomial
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_degree_two_dense_child_signal {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D 2)
    (k : nativeRationalTerminalIndex D L → ℤ) (hk : k ≠ 0)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    letI : MeasurableSpace (nativeRationalRelativeData D L 1).E := borel (nativeRationalRelativeData D L 1).E
    letI : MeasurableSpace (nativeRationalRelativeData D L 1).G := borel (nativeRationalRelativeData D L 1).G
    letI : MeasurableSpace (nativeRationalDegreeReducedData D L).E := borel (nativeRationalDegreeReducedData D L).E
    letI : MeasurableSpace (nativeRationalDegreeReducedData D L).G := borel (nativeRationalDegreeReducedData D L).G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ A Q S T : ℕ, 0 < A ∧ 0 < Q ∧ 0 < S ∧ 0 < T ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : Finset ((nativeRationalRelativeData D L 1).E →L[ℝ] ℝ),
      ∃ B : ℕ, 0 < B ∧ ∃ θ : ℝ, 0 < θ ∧
      (∀ χ ∈ C, NativeRationalNonlinearityCharacterGood D L χ →
        NativeRationalCharacterChildBudget D L k (A : ℝ) δ S χ B θ) ∧
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
                (roughVectorMvProjection χ.toLinearMap p) 2 J : ℝ) : UnitAddCircle)‖ ≤ (Q : ℝ)) ∨
        (∃ χ ∈ C,
          ∃ hHor : RoughNativeHorizontalFunctional (I := (nativeRationalRelativeData D L 1).I)
            (nativeRationalRelativeData D L 1).Γ χ.toLinearMap, ‖χ‖ ≤ (A : ℝ) ∧
          ∃ M : ℕ, 0 < M ∧ M ≤ S ∧
            (∀ j : ℕ, 2 ≤ j → j ≤ 2 → (N : ℝ)^j*
              ‖(((M : ℝ)*(nativeRationalCompactNonlinearScalar D L p hp χ).coeff j : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)) ∧
            (∀ j : ℕ, 2 ≤ j → j ≤ 2 → (N : ℝ)^j*
              ‖(((M : ℝ)*scalarPolynomialBinomialCoefficient
                (nativeRationalCompactNonlinearScalar D L p hp χ) 2 j : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)) ∧
            (∀ j : ℕ, 2 ≤ j → j ≤ 2 → (N : ℝ)^j*
              ‖(((M : ℝ)*(nativeRationalCompactDiagonalScalar D L p χ).coeff j : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)) ∧
            (∀ j : ℕ, 2 ≤ j → j ≤ 2 → (N : ℝ)^j*
              ‖(((M : ℝ)*scalarPolynomialBinomialCoefficient
                (nativeRationalCompactDiagonalScalar D L p χ) 2 j : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)) ∧
            ((N : ℝ)*‖(((M : ℝ)*(nativeRationalCompactDiagonalScalar D L p χ).eval 1 : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)) ∧
            ∃ b : NativeRationalFirstLayerIndex D L → ℤ,
              (∀ i, |(b i : ℝ)| ≤ (A : ℝ)) ∧
              nativeRationalRelativeDifferenceCharacter D L χ ≠ 0 ∧
              (∀ i, (nativeRationalIntegralCommutatorCharacter D L χ
                hHor.2.1 i).toLinearMap = 0) ∧
              (∀ g h : D.G, nativeRationalRelativeCommutatorValue D L χ g h = 0) ∧
              ∃ K : NativeRationalLieFiltration D 2,
                (∀ i, K.layer i = if 2 ≤ i then L.layer i ⊓
                  (nativeRationalDifferenceExtension D L χ).toLinearMap.ker else L.layer i) ∧
                Module.finrank ℝ (K.layer 2) < Module.finrank ℝ (L.layer 2) ∧
                nativeRationalFiltrationNonlinearity D K < nativeRationalFiltrationNonlinearity D L ∧
                (∃ (j : ℕ) (y : D.E) (q : ℕ), 2 ≤ j ∧ j ≤ 2 ∧ y ∈ L.layer j ∧
                  y ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ ∧
                  nativeRationalDifferenceExtension D L χ y=1 ∧
                  L.layer (j+1) ≤ (nativeRationalDifferenceExtension D L χ).toLinearMap.ker ∧
                  0 < q ∧ nativeLieExponential (E := D.E) (I := D.I) (G := D.G) y ^ q ∈ D.Γ ∧
                  (∃ (z : ℕ → ℤ) (E : ℝ[X]) (pK : RoughVectorMvPolynomial Unit D.E),
      E.natDegree ≤ j ∧ E.coeff 0=0 ∧ E.coeff 1=0 ∧
      (∀ i : ℕ, 2 ≤ i → i ≤ j → (M : ℝ)*(N : ℝ)^i*|E.coeff i| ≤ (A : ℝ)) ∧
      RoughVectorMvWeightedDegree K.layer pK 0 ∧ RoughVectorMvDegreeLE pK 2 ∧
      (∀ t : ℝ, nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (roughVectorMvEval (E := D.E) p (fun _ => t)) =
          nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (E.eval t • y)*
            nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) pK (fun _ => t))*
              nativeLieExponential (E := D.E) (I := D.I) (G := D.G) ((scalarNonlinearRationalPart j M z).eval t • y)) ∧
      (∀ (x t H : ℝ), 0 ≤ H → |x| ≤ (N : ℝ) → |t| ≤ (N : ℝ) → |x-t| ≤ H →
        (M : ℝ)*|E.eval x-E.eval t| ≤ ((j+1 : ℕ) : ℝ)^2*(A : ℝ)*(H/(N : ℝ))) ∧
      (∀ t : ℝ, |t| ≤ (N : ℝ) → |E.eval t| ≤ ((j+1 : ℕ) : ℝ)^2*(A : ℝ)) ∧
      (∀ n : ℕ, ∃ m ∈ Finset.range (M*q),
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (roughVectorMvEval (E := D.E) p (fun _ => (n : ℝ))) : D.G ⧸ D.Γ) =
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (E.eval (n : ℝ) • y)*
          nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
            (roughVectorMvEval (E := D.E) pK (fun _ => (n : ℝ)))*
              nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (((m : ℝ)/(M : ℝ)) • y) : D.G ⧸ D.Γ)) ∧
      (∀ n : ℕ, ∃ m ∈ Finset.range (M*q),
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) ((scalarNonlinearRationalPart j M z).eval (n : ℝ) • y) : D.G ⧸ D.Γ) =
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (((m : ℝ)/(M : ℝ)) • y) : D.G ⧸ D.Γ)) ∧
      ∀ a t : ℕ,
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) ((scalarNonlinearRationalPart j M z).eval ((a+M*q*t : ℕ) : ℝ) • y) : D.G ⧸ D.Γ) =
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) ((scalarNonlinearRationalPart j M z).eval (a : ℝ) • y) : D.G ⧸ D.Γ)) ∧
                  ∀ (p0 : RoughVectorMvPolynomial Unit D.E), RoughVectorMvWeightedDegree L.layer p0 0 →
                    ∃ pK : RoughVectorMvPolynomial Unit D.E, RoughVectorMvWeightedDegree K.layer pK 0 ∧
                      RoughVectorMvDegreeLE pK 2 ∧ ∀ x : Unit → ℝ,
                        nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) p0 x) =
                          nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
                            (MvPolynomial.eval x (unitMvNonlinearPart (roughVectorMvProjection
                              (nativeRationalDifferenceExtension D L χ).toLinearMap p0)) • y) *
                                nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) pK x)) ∧
              (∃ hHor : RoughNativeHorizontalFunctional (I := (nativeRationalRelativeData D L 1).I)
      (nativeRationalRelativeData D L 1).Γ χ.toLinearMap,
    ∃ hzero : ∀ g h : D.G, nativeRationalRelativeCommutatorValue D L χ g h=0,
    nativeRationalRelativeDifferenceCharacter D L χ ≠ 0 ∧
    let K0 := nativeRationalNonlinearKernelFiltration D L χ hHor hzero
    ∃ (j : ℕ) (y : D.E) (q K : ℕ),
      2 ≤ j ∧ j ≤ 2 ∧ y ∈ L.layer j ∧
      y ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ ∧
      nativeRationalDifferenceExtension D L χ y=1 ∧
      L.layer (j+1) ≤ (nativeRationalDifferenceExtension D L χ).toLinearMap.ker ∧
      0 < q ∧ nativeLieExponential (E := D.E) (I := D.I) (G := D.G) y ^ q ∈ D.Γ ∧
      0 < K ∧ q ≤ B ∧ K ≤ B ∧ ‖y‖ ≤ (B : ℝ) ∧ 4*K*(S*q) ≤ B ∧
          ∃ (a : ℤ) (T m : ℕ), 0 ≤ a ∧ a < (N : ℤ) ∧ 0 < T ∧ m < M*q ∧
            (N : ℝ)/(B : ℝ) ≤ T ∧
            let ρ := nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (((m : ℝ)/(M : ℝ)) • y)
            let Dm := nativeConjugateNilmanifoldData D ρ
            ∃ Km : NativeRationalLieFiltration Dm 2,
              (∀ i, Km.layer i=K0.layer i) ∧
              nativeRationalFiltrationNonlinearity Dm Km < nativeRationalFiltrationNonlinearity D L ∧
              ∃ pNew : RoughVectorMvPolynomial Unit D.E,
                RoughVectorMvWeightedDegree Km.layer pNew 0 ∧ RoughVectorMvDegreeLE pNew 2 ∧
                (∃ (z : ℕ → ℤ) (E : Polynomial ℝ) (pK : RoughVectorMvPolynomial Unit D.E),
                  E.natDegree ≤ j ∧ E.coeff 0=0 ∧ E.coeff 1=0 ∧
                  (∀ i : ℕ, 2 ≤ i → i ≤ j → (M : ℝ)*(N : ℝ)^i*|E.coeff i| ≤ (A : ℝ)) ∧
                  RoughVectorMvWeightedDegree K0.layer pK 0 ∧ RoughVectorMvDegreeLE pK 2 ∧
                  (∀ x : ℝ, nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
                    (roughVectorMvEval (E := D.E) p (fun _ => x))=
                    nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (E.eval x • y)*
                      nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) pK (fun _ => x))*
                        nativeLieExponential (E := D.E) (I := D.I) (G := D.G) ((scalarNonlinearRationalPart j M z).eval x • y)) ∧
                  pNew=nativeRationalProgressionPolynomial D pK a (M*q) ∧
                  ∀ n : ℤ, nativeMvPolynomialOrbit Dm pNew (fun _ => n)=
                    nativeMvPolynomialOrbit Dm pK (fun _ => a+((M*q : ℕ) : ℤ)*n)) ∧
                (letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := Dm.metric;
                 letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := Dm.metric.toUniformSpace.toTopologicalSpace;
                 ∃ J ∈ unitLipschitzObservables (D.G ⧸ roughConjugateSubgroup D.Γ ρ),
                   θ < ‖nativeNilmanifoldFiniteDiscrepancy Dm (scalarMvIntegerCube Unit T) (nativeMvPolynomialOrbit Dm pNew) J‖)) ∧
              ∃ V : Finset ℕ, V.Nonempty ∧ ρ*(N : ℝ) ≤ V.card ∧
                ∀ h ∈ V, 0 < h ∧ h < N ∧ NativeRationalRelativeCoefficientBounds D L p hp h χ N (A : ℝ) ∧
                  (N : ℝ)*‖((scalarFractionalBracket
                    (nativeRationalCompactBracketBeta D L p χ M b) (nativeRationalCompactBracketAlpha D L p hp χ M)
                    (nativeRationalCompactBracketCoefficient D L p χ M) (nativeRationalCompactBracketFrequency D L p)
                    (h : ℝ) : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)) := by
  exact native_rational_dense_child_signal D L (by omega)
    (native_rational_weighted_inverse_degree_one (nativeRationalDegreeReducedData D L)
      (nativeDegreeReducedRationalLieFiltration D L) Unit) k hk δ hδ hδ1

end Hindman168
