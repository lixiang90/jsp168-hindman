from pathlib import Path

src=Path('Hindman168/NativeRationalNonlinearityChildSignal.lean').read_text(encoding='utf-8')
header=src[:src.index(' := by')]
header=header[header.index('\n\n/-!'):]
header='import Hindman168.NativeRationalNonlinearityChildSignal'+header
header=header.replace('native_rational_nonlinearity_child_signal','native_rational_constructed_nonlinearity_child_signal')
a=header.index('/-!'); b=header.index('-/',a)+2
header=header[:a]+'''/-! GENUINE child UNIT signal now retains literal affine source
construction, not only quotient sample equality. Actual constructed source
has TRUE smaller weights/original degree and SAME UNIT discrepancy by
proved exact integer coset samples. No group equality is inferred from
coset equality; the new stronger source is actually CONSTRUCTED. -/'''+header[b:]
needle='''                  ∀ n : ℤ, nativeMvPolynomialOrbit Dm pNew (fun _ => n)='''
assert header.count(needle)==1
header=header.replace(needle,'''                  pNew=nativeRationalProgressionPolynomial D pK a (M*q) ∧
'''+needle)
body=''' := by
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
'''
Path('Hindman168/NativeRationalConstructedChildSignal.lean').write_text(header+body,encoding='utf-8')
