import Hindman168.NativeRationalIntegralCommutatorCharacter

/-! If all actual rational-basis candidate characters vanish, the ACTUAL
commutator pairing vanishes on EVERY pair of original group points. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators
universe u

theorem native_rational_integral_commutator_characters_zero_pairing {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker)
    (hzero : ∀ i, (nativeRationalIntegralCommutatorCharacter D L χ hχ i).toLinearMap = 0)
    (g h : D.G) : nativeRationalRelativeCommutatorValue D L χ g h = 0 := by
  have hcoeff (i : NativeRationalFirstLayerIndex D L) :
      nativeRationalCommutatorFirstLayerCoefficient D L χ g i = 0 := by
    have hz := DFunLike.congr_fun (hzero i)
      (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g)
    change nativeRationalIntegralCommutatorCharacter D L χ hχ i _ = 0 at hz
    rw [native_rational_integral_commutator_character_evaluation] at hz
    have hd : (nativeRationalSplitBasisDenominator D L : ℝ) ≠ 0 := by
      exact_mod_cast (native_rational_split_basis_denominator_positive D L).ne'
    have hp := (mul_eq_zero.mp hz).resolve_left hd
    change _/(nativeRationalFirstLayerDenominator D L : ℝ)=0
    rw [hp,zero_div]
  rw [native_rational_commutator_first_layer_evaluation D L χ hχ g h]
  apply Finset.sum_eq_zero
  intro i _
  rw [hcoeff,zero_mul]

end Hindman168
