import Hindman168.NativeRationalUniformOriginalTransport

/-! ACTUAL constructed child coefficient bounds and genuine source factors
produce one ORIGINAL nonzero horizontal/grid character with BOTH COMPLETE
original tables under a SINGLE source-independent budget. Child coefficients
are inputs for genuine later IH, not an added same-degree inverse premise. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_constructed_child_inverse_transport {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d S B : ℕ) (AK AE C : ℝ)
    (hB : 0 < B) (hAK : 0 ≤ AK) (hAE : 0 ≤ AE) (hC : 0 ≤ C) :
    ∃ Q : ℕ, 0 < Q ∧ ∀ (M q : ℕ), 0 < M → M ≤ S → 0 < q → q ≤ B →
      ∀ (ρ : D.G) (κ : D.E →L[ℝ] ℝ),
      RoughNativeHorizontalFunctional (I := D.I) (roughConjugateSubgroup D.Γ ρ) κ.toLinearMap → ‖κ‖ ≤ C →
      ∀ y : D.E, ‖y‖ ≤ (B : ℝ) →
      ∀ (p pK pNew : RoughVectorMvPolynomial Unit D.E) (j N T : ℕ) (a : ℤ)
        (z : ℕ → ℤ) (E : Polynomial ℝ),
      0 < N → 0 ≤ a → a < (N : ℤ) → (N : ℝ)/(B : ℝ) ≤ T →
      RoughVectorMvDegreeLE pK d →
      pNew=nativeRationalProgressionPolynomial D pK a (M*q) →
      E.natDegree ≤ j → E.coeff 1=0 →
      (∀ i : ℕ, 2 ≤ i → i ≤ j → (M : ℝ)*(N : ℝ)^i*|E.coeff i| ≤ AE) →
      nativeLieExponential (E := D.E) (I := D.I) (G := D.G) y ^ q ∈ D.Γ →
      (∀ x : ℝ,
        nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (roughVectorMvEval (E := D.E) p (fun _ => x)) =
        nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (E.eval x • y)*
          nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
            (roughVectorMvEval (E := D.E) pK (fun _ => x))*
          nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
            ((scalarNonlinearRationalPart j M z).eval x • y)) →
      (∀ I : Unit → ℕ, 0 < (∑ i, I i) →
        (T : ℝ)^(∑ i, I i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I)
          (roughVectorMvProjection κ.toLinearMap pNew) : ℝ) : UnitAddCircle)‖ ≤ AK) →
      ∃ χ : D.E →L[ℝ] ℝ,
        RoughNativeHorizontalFunctional (I := D.I) D.Γ χ.toLinearMap ∧ ‖χ‖ ≤ (Q : ℝ) ∧
        χ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (I := D.I) D.Γ (Q : ℝ) ∧
        (∀ I : Unit → ℕ, 0 < (∑ i, I i) →
          (N : ℝ)^(∑ i, I i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I)
            (roughVectorMvProjection χ.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ (Q : ℝ)) ∧
        ∀ I : Unit → ℕ, 0 < (∑ i, I i) →
          (N : ℝ)^(∑ i, I i)*‖((mvPolynomialBinomialCoefficient
            (roughVectorMvProjection χ.toLinearMap p) d I : ℝ) : UnitAddCircle)‖ ≤ (Q : ℝ) := by
  obtain ⟨Q,hQ,hUniform⟩ := native_rational_uniform_original_transport_character D d S B AK AE C hAK hAE hC
  refine ⟨Q,hQ,?_⟩
  intro M q hM hMS hq hqB ρ κ hHor hNorm y hy p pK pNew j N T a z E
    hN ha haN hLength hDegree hConstructed hEDegree hEOne hError hPower hExact hChild
  have hOriginal := (native_conjugate_horizontal_functional_iff D ρ κ.toLinearMap).mp hHor
  obtain ⟨hMono,_hBinomial⟩ := native_rational_original_coefficient_transport D κ hOriginal
    p pK pNew y d j M q B N T a z E AK AE hM hq hB hN ha haN hAK hAE hLength
    hDegree hConstructed hEDegree hEOne hError hPower hExact hChild
  exact hUniform M q hM hMS hq hqB κ hOriginal hNorm y hy p N hN hMono

end Hindman168
