import Hindman168.NativeRationalFrozenProgressionUnitSignal
import Hindman168.NativeRationalNonlinearRightFactors

/-! ACTUAL remaining nonlinearity branch now has GENUINE child UNIT
signal. Highest rational direction/lattice power, block budget and ONE
positive threshold are selected BEFORE every bounded multiplier/raw source.
Only PROVED source factors/freezing/partition/geometry/unit detection are
applied. No same-degree smaller-filtration inverse is assumed. -/
namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_nonlinearity_child_signal {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (hdeg : 2 ≤ ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hHor : RoughNativeHorizontalFunctional (I := (nativeRationalRelativeData D L 1).I)
      (nativeRationalRelativeData D L 1).Γ χ.toLinearMap)
    (hzero : ∀ g h : D.G, nativeRationalRelativeCommutatorValue D L χ g h=0)
    (hDiff : nativeRationalRelativeDifferenceCharacter D L χ ≠ 0)
    (k : nativeRationalTerminalIndex D L → ℤ) (hk : k ≠ 0)
    (A δ : ℝ) (S : ℕ) (hA : 0 ≤ A) (hδ : 0 < δ) (hS : 0 < S) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    let K0 := nativeRationalNonlinearKernelFiltration D L χ hHor hzero
    ∃ (j : ℕ) (y : D.E) (q K : ℕ) (θ : ℝ),
      2 ≤ j ∧ j ≤ ℓ ∧ y ∈ L.layer j ∧
      y ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ ∧
      nativeRationalDifferenceExtension D L χ y=1 ∧
      L.layer (j+1) ≤ (nativeRationalDifferenceExtension D L χ).toLinearMap.ker ∧
      0 < q ∧ nativeLieExponential (E := D.E) (I := D.I) (G := D.G) y ^ q ∈ D.Γ ∧
      0 < K ∧ 0 < θ ∧
      ∀ M : ℕ, 0 < M → M ≤ S → ∀ (p : RoughVectorMvPolynomial Unit D.E)
        (hp : RoughVectorMvWeightedDegree L.layer p 0) (N : ℕ), 4*K*(S*q) ≤ N →
        (∀ i : ℕ, 2 ≤ i → i ≤ ℓ → (N : ℝ)^i*
          ‖(((M : ℝ)*(nativeRationalCompactNonlinearScalar D L p hp χ).coeff i : ℝ) : UnitAddCircle)‖ ≤ A) →
        ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
          δ ≤ ‖finiteComplexSetMean (Finset.Ico 0 (N : ℤ)) (fun n =>
            nativeRationalTerminalFourierProjection D L k F (nativeMvPolynomialOrbit D p (fun _ => n)))‖ →
          ∃ (a : ℤ) (T m : ℕ), 0 ≤ a ∧ a < (N : ℤ) ∧ 0 < T ∧ m < M*q ∧
            (N : ℝ)/(4*(K : ℝ)*((S*q : ℕ) : ℝ)) ≤ T ∧
            let ρ := nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (((m : ℝ)/(M : ℝ)) • y)
            let Dm := nativeConjugateNilmanifoldData D ρ
            ∃ Km : NativeRationalLieFiltration Dm ℓ,
              (∀ i, Km.layer i=K0.layer i) ∧
              nativeRationalFiltrationNonlinearity Dm Km < nativeRationalFiltrationNonlinearity D L ∧
              ∃ pNew : RoughVectorMvPolynomial Unit D.E,
                RoughVectorMvWeightedDegree Km.layer pNew 0 ∧ RoughVectorMvDegreeLE pNew ℓ ∧
                (∃ (z : ℕ → ℤ) (E : Polynomial ℝ) (pK : RoughVectorMvPolynomial Unit D.E),
                  E.natDegree ≤ j ∧ E.coeff 0=0 ∧ E.coeff 1=0 ∧
                  (∀ i : ℕ, 2 ≤ i → i ≤ j → (M : ℝ)*(N : ℝ)^i*|E.coeff i| ≤ A) ∧
                  RoughVectorMvWeightedDegree K0.layer pK 0 ∧ RoughVectorMvDegreeLE pK ℓ ∧
                  (∀ x : ℝ, nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
                    (roughVectorMvEval (E := D.E) p (fun _ => x))=
                    nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (E.eval x • y)*
                      nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) pK (fun _ => x))*
                        nativeLieExponential (E := D.E) (I := D.I) (G := D.G) ((scalarNonlinearRationalPart j M z).eval x • y)) ∧
                  ∀ n : ℤ, nativeMvPolynomialOrbit Dm pNew (fun _ => n)=
                    nativeMvPolynomialOrbit Dm pK (fun _ => a+((M*q : ℕ) : ℤ)*n)) ∧
                (letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := Dm.metric;
                 letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := Dm.metric.toUniformSpace.toTopologicalSpace;
                 ∃ J ∈ unitLipschitzObservables (D.G ⧸ roughConjugateSubgroup D.Γ ρ),
                   θ < ‖nativeNilmanifoldFiniteDiscrepancy Dm (scalarMvIntegerCube Unit T) (nativeMvPolynomialOrbit Dm pNew) J‖) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  let K0 := nativeRationalNonlinearKernelFiltration D L χ hHor hzero
  obtain ⟨hDrop,j,y,q,hj2,hjL,hy,hyRat,hFy,hHigher,hq,hpow,_hUniversal⟩ :=
    native_rational_nonlinearity_exact_factorization D L hdeg χ hHor hzero hDiff
  obtain ⟨K,hK,θ,hθ,hSelect⟩ := native_rational_frozen_progression_unit_signal D L K0 hDrop
    k hk y hyRat j A δ S q hA hδ hS hq hpow
  refine ⟨j,y,q,K,θ,hj2,hjL,hy,hyRat,hFy,hHigher,hq,hpow,hK,hθ,?_⟩
  intro M hM hMS p hp N hLarge hBounds F hF hSignal
  have hSourceLarge : 4*K*(M*q) ≤ N :=
    (Nat.mul_le_mul_left (4*K) (Nat.mul_le_mul_right q hMS)).trans hLarge
  have hN : 0 < N := (show 0 < 4*K*(M*q) by positivity).trans_le hSourceLarge
  obtain ⟨z,E,pK,hED,h0,h1,hSmall,hWeighted,hDegree,hExact,_hVar,_hValue,_hWhole,_hResidues,_hPeriod⟩ :=
    native_rational_nonlinear_right_factors D L χ hHor hzero p hp j hj2 hjL y hy hFy hHigher
      q M N hq hM hN hpow A hA hBounds
  obtain ⟨a,T,m,_c,ha0,haN,hT,hm,hLength,_hC,pNew,hW,hD,hDropNew,hOrbit,_hZero,_hMean,J,hJ,hUnit⟩ :=
    hSelect M N hM hMS hSourceLarge z E p pK hED h0 h1 hSmall hWeighted hDegree hExact F hF hSignal
  have hLengthUniform : (N : ℝ)/(4*(K : ℝ)*((S*q : ℕ) : ℝ)) ≤ T :=
    (div_le_div_of_nonneg_left (Nat.cast_nonneg N) (by positivity)
      (show 4*(K : ℝ)*((M*q : ℕ) : ℝ) ≤ 4*(K : ℝ)*((S*q : ℕ) : ℝ) by
        exact_mod_cast Nat.mul_le_mul_left (4*K) (Nat.mul_le_mul_right q hMS))).trans hLength
  exact ⟨a,T,m,ha0,haN,hT,hm,hLengthUniform,
    nativeRationalResidueFiltration D K0 y hyRat M m,
    native_rational_residue_filtration_layer D K0 y hyRat M m,hDropNew,pNew,hW,hD,
    ⟨z,E,pK,hED,h0,h1,hSmall,hWeighted,hDegree,hExact,hOrbit⟩,J,hJ,hUnit⟩

end Hindman168
