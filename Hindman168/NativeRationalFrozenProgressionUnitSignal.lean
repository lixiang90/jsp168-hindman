import Hindman168.NativeRationalFrozenProgressionMean
import Hindman168.NativeRationalFiniteResidueUnitDetection
import Hindman168.NativeUnitCubePolynomialDiscrepancy

/-! ACTUAL original Fourier signal and genuine right factors yield a
TRUE smaller-filtration polynomial on standard child cube with LARGE
UNIT-observable canonical discrepancy. One positive threshold precedes
ALL bounded denominators/raw sources/N. No child inverse is assumed. -/
namespace Hindman168
open Polynomial MeasureTheory
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_frozen_progression_unit_signal {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L K0 : NativeRationalLieFiltration D ℓ)
    (hDrop : nativeRationalFiltrationNonlinearity D K0 < nativeRationalFiltrationNonlinearity D L)
    (k : nativeRationalTerminalIndex D L → ℤ) (hk : k ≠ 0) (y : D.E)
    (hyRat : y ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ) (j : ℕ)
    (A δ : ℝ) (S q : ℕ) (hA : 0 ≤ A) (hδ : 0 < δ) (hS : 0 < S) (hq : 0 < q)
    (hpow : nativeLieExponential (E := D.E) (I := D.I) (G := D.G) y ^ q ∈ D.Γ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ K : ℕ, 0 < K ∧ ∃ θ : ℝ, 0 < θ ∧ ∀ (M N : ℕ), 0 < M → M ≤ S → 4*K*(M*q) ≤ N →
      ∀ (z : ℕ → ℤ) (E : ℝ[X]) (p pK : RoughVectorMvPolynomial Unit D.E),
        E.natDegree ≤ j → E.coeff 0=0 → E.coeff 1=0 →
        (∀ i : ℕ, 2 ≤ i → i ≤ j → (M : ℝ)*(N : ℝ)^i*|E.coeff i| ≤ A) →
        RoughVectorMvWeightedDegree K0.layer pK 0 → RoughVectorMvDegreeLE pK ℓ →
        (∀ x : ℝ, nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (roughVectorMvEval (E := D.E) p (fun _ => x))=
          nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (E.eval x • y)*
            nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) pK (fun _ => x))*
              nativeLieExponential (E := D.E) (I := D.I) (G := D.G) ((scalarNonlinearRationalPart j M z).eval x • y)) →
        ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
          δ ≤ ‖finiteComplexSetMean (Finset.Ico 0 (N : ℤ)) (fun n =>
            nativeRationalTerminalFourierProjection D L k F (nativeMvPolynomialOrbit D p (fun _ => n)))‖ →
          ∃ (a : ℤ) (T m : ℕ) (c : ℝ),
            0 ≤ a ∧ a < (N : ℤ) ∧ 0 < T ∧ m < M*q ∧
            (N : ℝ)/(4*(K : ℝ)*((M*q : ℕ) : ℝ)) ≤ T ∧ |c| ≤ ((j+1 : ℕ) : ℝ)^2*A ∧
            let ρ := nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (((m : ℝ)/(M : ℝ)) • y)
            let Dm := nativeConjugateNilmanifoldData D ρ
            let Km := nativeRationalResidueFiltration D K0 y hyRat M m
            letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := Dm.metric
            letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := Dm.metric.toUniformSpace.toTopologicalSpace
            let H := nativeConjugateFourierObservable D L k ρ
              (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (c • y)) F
            ∃ pNew : RoughVectorMvPolynomial Unit D.E,
              RoughVectorMvWeightedDegree Km.layer pNew 0 ∧ RoughVectorMvDegreeLE pNew ℓ ∧
              nativeRationalFiltrationNonlinearity Dm Km < nativeRationalFiltrationNonlinearity D L ∧
              (∀ n : ℤ, nativeMvPolynomialOrbit Dm pNew (fun _ => n)=nativeMvPolynomialOrbit Dm pK (fun _ => a+((M*q : ℕ) : ℤ)*n)) ∧
              (∫ q0, H q0 ∂nativeNilmanifoldQuotientProbability Dm)=0 ∧
              δ/2 < ‖finiteComplexSetMean (Finset.Ico 0 (T : ℤ)) (fun n => H (nativeMvPolynomialOrbit Dm pNew (fun _ => n)))‖ ∧
              ∃ J ∈ unitLipschitzObservables (D.G ⧸ roughConjugateSubgroup D.Γ ρ),
                θ < ‖nativeNilmanifoldFiniteDiscrepancy Dm (scalarMvIntegerCube Unit T) (nativeMvPolynomialOrbit Dm pNew) J‖ := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨K,hK,hSelect⟩ := native_rational_frozen_progression_mean D L K0 hDrop k hk y hyRat j A δ hA hδ
  obtain ⟨θ,hθ,hDetect⟩ := native_rational_finite_residue_unit_detection D L k hk y
    (((j+1 : ℕ) : ℝ)^2*A) (δ/2) S q (by positivity) hS hq
  refine ⟨K,hK,θ,hθ,?_⟩
  intro M N hM hMS hLarge z E p pK hED h0 h1 hBounds hpK hpKD hExact F hF hSignal
  obtain ⟨a,T,m,c,ha0,haN,hT,hm,hLength,hC,pNew,hWeights,hDegree,hDropNew,hOrbit,hZero,hMean⟩ :=
    hSelect M q N hM hq hLarge hpow z E p pK hED h0 h1 hBounds hpK hpKD hExact F hF hSignal
  let ρ := nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (((m : ℝ)/(M : ℝ)) • y)
  let Dm := nativeConjugateNilmanifoldData D ρ
  letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := Dm.metric
  letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := Dm.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨J,hJ,hUnit⟩ := hDetect M hM hMS m hm (Finset.Ico 0 (T : ℤ))
    (fun n => nativeMvPolynomialOrbit Dm pNew (fun _ => n)) c hC F hF hMean.le
  refine ⟨a,T,m,c,ha0,haN,hT,hm,hLength,hC,pNew,hWeights,hDegree,hDropNew,hOrbit,hZero,hMean,J,hJ,?_⟩
  have hCube := native_unit_cube_polynomial_discrepancy Dm pNew T J
  exact hUnit.trans_eq (congrArg norm hCube.symm)

end Hindman168
