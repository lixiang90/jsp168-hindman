import Hindman168.NativeRationalFiniteInverseBudget
import Hindman168.NativeRationalResidueFiltration

/-! All ACTUAL bounded denominator/residue conjugated children have one
full inverse budget from legitimate smaller-nonlinearity IH. Canonical child
data are fixed before p/N, including harmless dummy zero denominators. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_residue_inverse_budget {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L K : NativeRationalLieFiltration D ℓ)
    (hDrop : nativeRationalFiltrationNonlinearity D K < nativeRationalFiltrationNonlinearity D L)
    (hIH : ∀ (D' : NativeNilmanifoldData.{u} s) (L' : NativeRationalLieFiltration D' ℓ),
      nativeRationalFiltrationNonlinearity D' L' < nativeRationalFiltrationNonlinearity D L →
      NativeRationalWeightedInverseStatement D' L' Unit)
    (y : D.E) (hy : y ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ)
    (S q : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℕ, 0 < C ∧ ∀ M : ℕ, M ≤ S → ∀ m : ℕ, m < M*q →
      let ρ := nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (((m : ℝ)/(M : ℝ)) • y)
      let Dm := nativeConjugateNilmanifoldData D ρ
      let Km := nativeRationalResidueFiltration D K y hy M m
      letI : MeasurableSpace Dm.E := borel Dm.E
      letI : MeasurableSpace Dm.G := borel Dm.G
      letI := Dm.metric
      letI : TopologicalSpace (Dm.G ⧸ Dm.Γ) := Dm.metric.toUniformSpace.toTopologicalSpace
      ∀ p : RoughVectorMvPolynomial Unit Dm.E,
      RoughVectorMvWeightedDegree Km.layer p 0 → ∀ N : ℕ, 0 < N →
      ∀ H ∈ unitLipschitzObservables (Dm.G ⧸ Dm.Γ),
        δ ≤ ‖nativeNilmanifoldFiniteDiscrepancy Dm (scalarMvIntegerCube Unit N)
          (nativeMvPolynomialOrbit Dm p) H‖ →
        ∃ χ : Dm.E →L[ℝ] ℝ,
          RoughNativeHorizontalFunctional (I := Dm.I) Dm.Γ χ.toLinearMap ∧ ‖χ‖ ≤ (C : ℝ) ∧
          χ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (I := Dm.I) Dm.Γ (C : ℝ) ∧
          (∀ J : Unit → ℕ, 0 < (∑ j, J j) →
            (N : ℝ)^(∑ j, J j)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J)
              (roughVectorMvProjection χ.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ (C : ℝ)) ∧
          ∀ J : Unit → ℕ, 0 < (∑ j, J j) →
            (N : ℝ)^(∑ j, J j)*‖((mvPolynomialBinomialCoefficient
              (roughVectorMvProjection χ.toLinearMap p) ℓ J : ℝ) : UnitAddCircle)‖ ≤ (C : ℝ) := by
  let I := Fin (S+1) × Fin (S*q)
  let Dchild (i : I) := nativeConjugateNilmanifoldData D
    (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (((i.2.val : ℝ)/(i.1.val : ℝ)) • y))
  let Lchild (i : I) : NativeRationalLieFiltration (Dchild i) ℓ :=
    nativeRationalResidueFiltration D K y hy i.1.val i.2.val
  have hEach (i : I) : NativeRationalWeightedInverseStatement (Dchild i) (Lchild i) Unit :=
    hIH (Dchild i) (Lchild i)
      (native_rational_residue_filtration_nonlinearity_lt D L K hDrop y hy i.1.val i.2.val)
  obtain ⟨C,hC,hAll⟩ := native_rational_finite_inverse_budget Dchild Lchild hEach δ hδ
  refine ⟨C,hC,?_⟩
  intro M hMS m hm
  let i : I := ⟨⟨M,by omega⟩,⟨m,hm.trans_le (Nat.mul_le_mul_right q hMS)⟩⟩
  exact hAll i

end Hindman168
