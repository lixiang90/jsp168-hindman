import Hindman168.NativeRationalCommutatorFirstLayer
import Hindman168.NativeRationalSelectedRepresentatives
import Hindman168.NativeRationalCompactNormalizedPolynomial

/-! Actual commutator coefficient operator bound on the SAME fixed compact
representative set. The budget precedes every character and source input. -/
namespace Hindman168
open scoped Manifold ContDiff Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalRelativeCommutatorModel {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (a g : D.G) :
    (nativeRationalRelativeData D L 1).E :=
  nativeLieGlobalLogarithm (E := (nativeRationalRelativeData D L 1).E)
    (I := (nativeRationalRelativeData D L 1).I) (G := (nativeRationalRelativeData D L 1).G)
    (nativeRationalRelativeFirstDifferenceGroup D L
      (subgroupCommElement _ (native_rational_original_commutator_mem_two D L) a g))

theorem native_rational_relative_commutator_model_continuous {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (g : D.G) :
    Continuous (fun a => nativeRationalRelativeCommutatorModel D L a g) := by
  apply (nativeLieGlobalLogarithm (E := (nativeRationalRelativeData D L 1).E)
    (I := (nativeRationalRelativeData D L 1).I) (G := (nativeRationalRelativeData D L 1).G)).continuous.comp
  apply Continuous.subtype_mk
  change Continuous (fun a : D.G => (a*g*a⁻¹*g⁻¹,(1 : D.G)))
  exact (((continuous_id.mul continuous_const).mul continuous_inv).mul continuous_const).prodMk continuous_const

theorem native_rational_commutator_coefficient_bound {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
      (a : D.G), a ∈ nativeRationalRepresentativeSet D →
        ∀ i, |nativeRationalCommutatorFirstLayerCoefficient D L χ a i| ≤ ‖χ‖*B := by
  let e (i : NativeRationalFirstLayerIndex D L) := nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
    (nativeRationalFirstLayerRealBasis D L (Sum.inr i))
  let f (a : D.G) : NativeRationalFirstLayerIndex D L → ℝ :=
    fun i => ‖nativeRationalRelativeCommutatorModel D L a (e i)‖
  have hf : Continuous f := continuous_pi (fun i => (native_rational_relative_commutator_model_continuous D L (e i)).norm)
  obtain ⟨b,hb⟩ := (native_rational_representative_set_compact D).bddAbove_image hf.norm.continuousOn
  let B := max b 0
  refine ⟨B,le_max_right _ _,?_⟩
  intro χ a ha i
  have hm : ‖nativeRationalRelativeCommutatorModel D L a (e i)‖ ≤ B := by
    have hi := norm_le_pi_norm (f a) i
    have hi' : ‖nativeRationalRelativeCommutatorModel D L a (e i)‖ ≤ ‖f a‖ := by
      simpa only [f,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] using hi
    exact hi'.trans ((hb (Set.mem_image_of_mem _ ha)).trans (le_max_left _ _))
  have hq : (1 : ℝ) ≤ (nativeRationalFirstLayerDenominator D L : ℝ) := by
    exact_mod_cast native_rational_first_layer_denominator_positive D L
  have hq0 := lt_of_lt_of_le zero_lt_one hq
  change |χ (nativeRationalRelativeCommutatorModel D L a (e i))/(nativeRationalFirstLayerDenominator D L : ℝ)| ≤ _
  rw [abs_div,abs_of_pos hq0]
  apply (div_le_iff₀ hq0).mpr
  have hv : |χ (nativeRationalRelativeCommutatorModel D L a (e i))| ≤ ‖χ‖*B :=
    (show |χ (nativeRationalRelativeCommutatorModel D L a (e i))| ≤
        ‖χ‖*‖nativeRationalRelativeCommutatorModel D L a (e i)‖ by
      simpa only [Real.norm_eq_abs] using χ.le_opNorm (nativeRationalRelativeCommutatorModel D L a (e i))).trans
      (mul_le_mul_of_nonneg_left hm (norm_nonneg χ))
  exact hv.trans (le_mul_of_one_le_right (mul_nonneg (norm_nonneg χ) (le_max_right _ _)) hq)

theorem native_rational_compact_commutator_coefficient_bound {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (p : RoughVectorMvPolynomial Unit D.E)
      (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ), ∀ i,
        |nativeRationalCommutatorFirstLayerCoefficient D L χ
          (nativeIntegerLogPolynomialSequence D (nativeRationalCompactNormalizedPolynomial D p) 1) i| ≤ ‖χ‖*B := by
  obtain ⟨B,hB,hbound⟩ := native_rational_commutator_coefficient_bound D L
  refine ⟨B,hB,?_⟩
  intro p χ i
  apply hbound χ _ ?_ i
  rw [native_rational_compact_normalized_polynomial_one]
  exact native_rational_representative_mem D _

end Hindman168
