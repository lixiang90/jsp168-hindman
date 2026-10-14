import Hindman168.NativeRationalCompactBracketParameters

/-! All actual useful-density and circle-error inputs transport to the SAME
fractional bracket on a subset with common actual integer offsets. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_dense_fractional_input {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ∃ K : ℕ,
      ∀ (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
        (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ),
        nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
          (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker →
        ∀ (M N : ℕ) (B : ℝ) (U : Finset ℕ), U.Nonempty → ρ*(N : ℝ) ≤ U.card →
          (∀ h ∈ U, (N : ℝ)*‖(((M : ℝ)*((nativeRationalCompactDiagonalScalar D L p χ).eval 1+
            scalarPolynomialBinomialCoefficient (nativeRationalCompactNonlinearScalar D L p hp χ) ℓ 2*(h : ℝ)+
            nativeRationalCompactCommutatorSlope D L p χ h) : ℝ) : UnitAddCircle)‖ ≤ B) →
          ∃ (b : NativeRationalFirstLayerIndex D L → ℤ), (∀ i, |(b i : ℝ)| ≤ (K : ℝ)) ∧
            ∃ V : Finset ℕ, V ⊆ U ∧ V.Nonempty ∧ ρ'*(N : ℝ) ≤ V.card ∧
              ∀ h ∈ V, (N : ℝ)*‖((scalarFractionalBracket
                (nativeRationalCompactBracketBeta D L p χ M b) (nativeRationalCompactBracketAlpha D L p hp χ M)
                (nativeRationalCompactBracketCoefficient D L p χ M) (nativeRationalCompactBracketFrequency D L p)
                (h : ℝ) : ℝ) : UnitAddCircle)‖ ≤ B := by
  obtain ⟨K,C,hC,hbound,hselect⟩ := native_rational_dense_compact_fractional_slope D L
  have hc : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
  refine ⟨ρ/(C.card : ℝ),div_pos hρ hc,K,?_⟩
  intro p hp χ hχ M N B U hU hsize hsmall
  obtain ⟨b,hb,V,hVU,hV,hcard,he⟩ := hselect p χ hχ U hU
  refine ⟨b,hbound b hb,V,hVU,hV,finite_refinement_density ρ (N : ℝ) C.card U.card V.card hc hsize hcard,?_⟩
  intro h hh
  have he' := he h hh ((nativeRationalCompactDiagonalScalar D L p χ).eval 1)
    (scalarPolynomialBinomialCoefficient (nativeRationalCompactNonlinearScalar D L p hp χ) ℓ 2) (M : ℝ)
  change (M : ℝ)*_ = scalarFractionalBracket (nativeRationalCompactBracketBeta D L p χ M b)
    (nativeRationalCompactBracketAlpha D L p hp χ M) (nativeRationalCompactBracketCoefficient D L p χ M)
    (nativeRationalCompactBracketFrequency D L p) (h : ℝ) at he'
  rw [← he']
  exact hsmall h (hVU hh)

end Hindman168
