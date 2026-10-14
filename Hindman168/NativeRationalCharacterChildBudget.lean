import Hindman168.NativeRationalConstructedChildSignal
import Hindman168.FiniteConditionedSignalBudgets

/-! Named ACTUAL child-budget proposition is PROVED for every valid
character. It retains genuine geometry/source relations and UNIT signal.
This is not a datum field, inverse premise or formalization target. -/
namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

def NativeRationalNonlinearityCharacterGood {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) : Prop :=
  RoughNativeHorizontalFunctional (I := (nativeRationalRelativeData D L 1).I)
    (nativeRationalRelativeData D L 1).Γ χ.toLinearMap ∧
    (∀ g h : D.G, nativeRationalRelativeCommutatorValue D L χ g h=0) ∧
      nativeRationalRelativeDifferenceCharacter D L χ ≠ 0

def NativeRationalCharacterChildBudget {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) (A δ : ℝ) (S : ℕ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) (B : ℕ) (θ : ℝ) : Prop :=
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ hHor : RoughNativeHorizontalFunctional (I := (nativeRationalRelativeData D L 1).I)
      (nativeRationalRelativeData D L 1).Γ χ.toLinearMap,
    ∃ hzero : ∀ g h : D.G, nativeRationalRelativeCommutatorValue D L χ g h=0,
    nativeRationalRelativeDifferenceCharacter D L χ ≠ 0 ∧
    let K0 := nativeRationalNonlinearKernelFiltration D L χ hHor hzero
    ∃ (j : ℕ) (y : D.E) (q K : ℕ),
      2 ≤ j ∧ j ≤ ℓ ∧ y ∈ L.layer j ∧
      y ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ ∧
      nativeRationalDifferenceExtension D L χ y=1 ∧
      L.layer (j+1) ≤ (nativeRationalDifferenceExtension D L χ).toLinearMap.ker ∧
      0 < q ∧ nativeLieExponential (E := D.E) (I := D.I) (G := D.G) y ^ q ∈ D.Γ ∧
      0 < K ∧ q ≤ B ∧ K ≤ B ∧ ‖y‖ ≤ (B : ℝ) ∧ 4*K*(S*q) ≤ B ∧
      ∀ M : ℕ, 0 < M → M ≤ S → ∀ (p : RoughVectorMvPolynomial Unit D.E)
        (hp : RoughVectorMvWeightedDegree L.layer p 0) (N : ℕ), B ≤ N →
        (∀ i : ℕ, 2 ≤ i → i ≤ ℓ → (N : ℝ)^i*
          ‖(((M : ℝ)*(nativeRationalCompactNonlinearScalar D L p hp χ).coeff i : ℝ) : UnitAddCircle)‖ ≤ A) →
        ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
          δ ≤ ‖finiteComplexSetMean (Finset.Ico 0 (N : ℤ)) (fun n =>
            nativeRationalTerminalFourierProjection D L k F (nativeMvPolynomialOrbit D p (fun _ => n)))‖ →
          ∃ (a : ℤ) (T m : ℕ), 0 ≤ a ∧ a < (N : ℤ) ∧ 0 < T ∧ m < M*q ∧
            (N : ℝ)/(B : ℝ) ≤ T ∧
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
                  pNew=nativeRationalProgressionPolynomial D pK a (M*q) ∧
                  ∀ n : ℤ, nativeMvPolynomialOrbit Dm pNew (fun _ => n)=
                    nativeMvPolynomialOrbit Dm pK (fun _ => a+((M*q : ℕ) : ℤ)*n)) ∧
                (letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := Dm.metric;
                 letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := Dm.metric.toUniformSpace.toTopologicalSpace;
                 ∃ J ∈ unitLipschitzObservables (D.G ⧸ roughConjugateSubgroup D.Γ ρ),
                   θ < ‖nativeNilmanifoldFiniteDiscrepancy Dm (scalarMvIntegerCube Unit T) (nativeMvPolynomialOrbit Dm pNew) J‖)

theorem native_rational_character_child_budget_exists {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (hdeg : 2 ≤ ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) (hk : k ≠ 0) (A δ : ℝ) (S : ℕ)
    (hA : 0 ≤ A) (hδ : 0 < δ) (hS : 0 < S)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) (hGood : NativeRationalNonlinearityCharacterGood D L χ) :
    ∃ B : ℕ, 0 < B ∧ ∃ θ : ℝ, 0 < θ ∧ NativeRationalCharacterChildBudget D L k A δ S χ B θ := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨hHor,hzero,hDiff⟩ := hGood
  obtain ⟨j,y,q,K,θ,hj2,hjL,hy,hyRat,hFy,hHigher,hq,hpow,hK,hθ,hSelect⟩ :=
    native_rational_constructed_nonlinearity_child_signal D L hdeg χ hHor hzero hDiff k hk A δ S hA hδ hS
  let B := 4*K*(S*q)+⌈‖y‖⌉₊+q+K+1
  have hB : 0 < B := by dsimp only [B]; omega
  have h4B : 4*K*(S*q) ≤ B := by dsimp only [B]; omega
  have hqB : q ≤ B := by dsimp only [B]; omega
  have hKB : K ≤ B := by dsimp only [B]; omega
  have hyB : ‖y‖ ≤ (B : ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast (show ⌈‖y‖⌉₊ ≤ B by dsimp only [B]; omega))
  refine ⟨B,hB,θ,hθ,hHor,hzero,hDiff,j,y,q,K,hj2,hjL,hy,hyRat,hFy,hHigher,hq,hpow,hK,hqB,hKB,hyB,h4B,?_⟩
  intro M hM hMS p hp N hBN hBounds F hF hSignal
  obtain ⟨a,T,m,ha0,haN,hT,hm,hLength,hRest⟩ :=
    hSelect M hM hMS p hp N (h4B.trans hBN) hBounds F hF hSignal
  have hLengthB : (N : ℝ)/(B : ℝ) ≤ T :=
    (div_le_div_of_nonneg_left (Nat.cast_nonneg N) (by positivity)
      (by exact_mod_cast h4B)).trans hLength
  exact ⟨a,T,m,ha0,haN,hT,hm,hLengthB,hRest⟩

theorem native_rational_character_child_budget_mono {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) (A δ : ℝ) (S : ℕ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) (B B' : ℕ) (θ θ' : ℝ)
    (hB : 0 < B) (hBB : B ≤ B') (hθ : θ' ≤ θ)
    (hData : NativeRationalCharacterChildBudget D L k A δ S χ B θ) :
    NativeRationalCharacterChildBudget D L k A δ S χ B' θ' := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨hHor,hzero,hDiff,j,y,q,K,hj2,hjL,hy,hyRat,hFy,hHigher,hq,hpow,hK,hqB,hKB,hyB,h4B,hSelect⟩ := hData
  refine ⟨hHor,hzero,hDiff,j,y,q,K,hj2,hjL,hy,hyRat,hFy,hHigher,hq,hpow,hK,
    hqB.trans hBB,hKB.trans hBB,hyB.trans (by exact_mod_cast hBB),h4B.trans hBB,?_⟩
  intro M hM hMS p hp N hBN hBounds F hF hSignal
  obtain ⟨a,T,m,ha0,haN,hT,hm,hLength,Km,hLayers,hDrop,pNew,hW,hD,hFactors,J,hJ,hUnit⟩ :=
    hSelect M hM hMS p hp N (hBB.trans hBN) hBounds F hF hSignal
  have hLengthB' : (N : ℝ)/(B' : ℝ) ≤ T :=
    (div_le_div_of_nonneg_left (Nat.cast_nonneg N) (by exact_mod_cast hB)
      (by exact_mod_cast hBB)).trans hLength
  exact ⟨a,T,m,ha0,haN,hT,hm,hLengthB',Km,hLayers,hDrop,pNew,hW,hD,hFactors,J,hJ,hθ.trans_lt hUnit⟩

end Hindman168
