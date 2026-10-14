import Hindman168.NativeRationalCommutatorFirstLayer
import Hindman168.NativeRationalDenseRepresentativeRefinement
import Hindman168.NativeRationalCompactUnivariateScalars

/-! Exact fractional-part expression for the ACTUAL compact commutator
slope on a dense refinement of SAME useful shifts, including the actual
integer-offset correction. No bracket-polynomial inverse is assumed. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_fractional_commutator_evaluation {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker)
    (a : D.G) (h : ℕ) (b : NativeRationalFirstLayerIndex D L → ℤ)
    (he : ∀ i, nativeRationalFirstLayerCoordinates D L (nativeRationalRepresentative D (a^(h : ℤ))) i =
      Int.fract ((h : ℝ)*nativeRationalFirstLayerCoordinates D L a i)+(b i : ℝ)) :
    nativeRationalRelativeCommutatorValue D L χ a (nativeRationalRepresentative D (a^(h : ℤ))) =
      (∑ i, nativeRationalCommutatorFirstLayerCoefficient D L χ a i*
        Int.fract ((h : ℝ)*nativeRationalFirstLayerCoordinates D L a i))+
      ∑ i, nativeRationalCommutatorFirstLayerCoefficient D L χ a i*(b i : ℝ) := by
  rw [native_rational_commutator_first_layer_evaluation D L χ hχ]
  simp_rw [he,mul_add]
  exact Finset.sum_add_distrib

theorem scalar_fractional_bracket_scaling {ι : Type*} [Fintype ι]
    (β α M h : ℝ) (ζ γ : ι → ℝ) (b : ι → ℤ) :
    M*(β+α*h+((∑ i, ζ i*Int.fract (h*γ i))+∑ i, ζ i*(b i : ℝ))) =
      (M*β+∑ i, (M*ζ i)*(b i : ℝ))+(M*α)*h+
        ∑ i, (M*ζ i)*Int.fract (h*γ i) := by
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum,← Finset.mul_sum]
  ring

theorem native_rational_dense_compact_fractional_slope {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    ∃ K : ℕ, ∃ C : Finset (NativeRationalFirstLayerIndex D L → ℤ), C.Nonempty ∧
      (∀ b ∈ C, ∀ i, |(b i : ℝ)| ≤ (K : ℝ)) ∧
      ∀ (p : RoughVectorMvPolynomial Unit D.E)
        (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ),
        nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
          (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker →
        ∀ (U : Finset ℕ), U.Nonempty →
          ∃ b ∈ C, ∃ V : Finset ℕ, V ⊆ U ∧ V.Nonempty ∧
            (U.card : ℝ) ≤ (C.card : ℝ)*(V.card : ℝ) ∧
            ∀ h ∈ V, ∀ (β α M : ℝ),
              let a := nativeIntegerLogPolynomialSequence D (nativeRationalCompactNormalizedPolynomial D p) 1
              M*(β+α*(h : ℝ)+nativeRationalCompactCommutatorSlope D L p χ h) =
                (M*β+∑ i, (M*nativeRationalCommutatorFirstLayerCoefficient D L χ a i)*(b i : ℝ))+
                  (M*α)*(h : ℝ)+∑ i, (M*nativeRationalCommutatorFirstLayerCoefficient D L χ a i)*
                    Int.fract ((h : ℝ)*nativeRationalFirstLayerCoordinates D L a i) := by
  obtain ⟨K,C,hC,hbound,hselect⟩ := native_rational_dense_representative_refinement D L
  refine ⟨K,C,hC,hbound,?_⟩
  intro p χ hχ U hU
  let a := nativeIntegerLogPolynomialSequence D (nativeRationalCompactNormalizedPolynomial D p) 1
  obtain ⟨b,hb,V,hVU,hV,hcard,he⟩ := hselect a U hU
  refine ⟨b,hb,V,hVU,hV,hcard,?_⟩
  intro h hh β α M
  change M*(β+α*(h : ℝ)+nativeRationalRelativeCommutatorValue D L χ a
    (nativeRationalRepresentative D (a^(h : ℤ)))) = _
  rw [native_rational_fractional_commutator_evaluation D L χ hχ a h b (he h hh)]
  exact scalar_fractional_bracket_scaling β α M (h : ℝ) _ _ b

end Hindman168
