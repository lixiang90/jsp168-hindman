import Hindman168.NativeRationalNonlinearityChildSignal

/-! GENUINE child UNIT signal now retains literal affine source
construction, not only quotient sample equality. Actual constructed source
has TRUE smaller weights/original degree and SAME UNIT discrepancy by
proved exact integer coset samples. No group equality is inferred from
coset equality; the new stronger source is actually CONSTRUCTED. -/
namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_constructed_nonlinearity_child_signal {s ℓ : ℕ}
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
                  pNew=nativeRationalProgressionPolynomial D pK a (M*q) ∧
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
  obtain ⟨j,y,q,K,θ,hj2,hjL,hy,hyRat,hFy,hHigher,hq,hpow,hK,hθ,hSelect⟩ :=
    native_rational_nonlinearity_child_signal D L hdeg χ hHor hzero hDiff k hk A δ S hA hδ hS
  refine ⟨j,y,q,K,θ,hj2,hjL,hy,hyRat,hFy,hHigher,hq,hpow,hK,hθ,?_⟩
  intro M hM hMS p hp N hLarge hBounds F hF hSignal
  obtain ⟨a,T,m,ha0,haN,hT,hm,hLength,Km,hLayers,hDrop,pOld,hOldW,_hOldD,
      ⟨z,E,pK,hED,h0,h1,hSmall,hW,hD,hExact,hOrbit⟩,J,hJ,hUnit⟩ :=
    hSelect M hM hMS p hp N hLarge hBounds F hF hSignal
  let ρ := nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (((m : ℝ)/(M : ℝ)) • y)
  let Dm := nativeConjugateNilmanifoldData D ρ
  letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := Dm.metric
  letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := Dm.metric.toUniformSpace.toTopologicalSpace
  let pNew := nativeRationalProgressionPolynomial D pK a (M*q)
  have hNewW : RoughVectorMvWeightedDegree Km.layer pNew 0 := by
    have hw := native_rational_progression_polynomial_weighted D K0 pK hW a (M*q)
    intro t ht
    rw [hLayers]
    exact hw t ht
  have hNewD : RoughVectorMvDegreeLE pNew ℓ := native_rational_progression_polynomial_degree D pK ℓ hD a (M*q)
  have hNewOrbit (n : ℤ) : nativeMvPolynomialOrbit Dm pNew (fun _ => n)=
      nativeMvPolynomialOrbit Dm pK (fun _ => a+((M*q : ℕ) : ℤ)*n) :=
    native_rational_progression_polynomial_orbit Dm pK a (M*q) n
  have hSame (x : Unit → ℤ) : nativeMvPolynomialOrbit Dm pNew x=nativeMvPolynomialOrbit Dm pOld x := by
    have hx : x=(fun _ => x ()) := by funext i; cases i; rfl
    calc
      _ = nativeMvPolynomialOrbit Dm pNew (fun _ => x ()) := congrArg (nativeMvPolynomialOrbit Dm pNew) hx
      _ = nativeMvPolynomialOrbit Dm pK (fun _ => a+((M*q : ℕ) : ℤ)*x ()) := hNewOrbit (x ())
      _ = nativeMvPolynomialOrbit Dm pOld (fun _ => x ()) := (hOrbit (x ())).symm
      _ = _ := (congrArg (nativeMvPolynomialOrbit Dm pOld) hx).symm
  have hDiscrep : nativeNilmanifoldFiniteDiscrepancy Dm (scalarMvIntegerCube Unit T)
      (nativeMvPolynomialOrbit Dm pOld) J=
      nativeNilmanifoldFiniteDiscrepancy Dm (scalarMvIntegerCube Unit T) (nativeMvPolynomialOrbit Dm pNew) J := by
    change finiteComplexSetMean _ (fun x => J (nativeMvPolynomialOrbit Dm pOld x))-_=
      finiteComplexSetMean _ (fun x => J (nativeMvPolynomialOrbit Dm pNew x))-_
    congr 1
    apply congrArg (finiteComplexSetMean (scalarMvIntegerCube Unit T))
    funext x
    exact congrArg J (hSame x).symm
  exact ⟨a,T,m,ha0,haN,hT,hm,hLength,Km,hLayers,hDrop,pNew,hNewW,hNewD,
    ⟨z,E,pK,hED,h0,h1,hSmall,hW,hD,hExact,rfl,hNewOrbit⟩,J,hJ,
    hUnit.trans_eq (congrArg norm hDiscrep)⟩

end Hindman168
