import Hindman168.NativeRationalCommutatorCharacter
import Hindman168.NativeRationalFirstLayerEvaluation
import Hindman168.SubgroupRealCommutatorKernel
import Hindman168.NativeContinuousCharacterLinearization

/-! The genuine relative commutator observable factors through G/F_2.
Its coefficients are actual evaluations on the fixed rational split basis. -/
namespace Hindman168
open scoped Manifold ContDiff commutatorElement BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_commutator_character_continuous {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) (a : D.G) :
    Continuous (nativeRationalRelativeCommutatorValue D L χ a) := by
  apply (nativeRationalRelativeDifferenceLogCharacter D L χ).continuous.comp
  apply Continuous.subtype_mk
  change Continuous (fun g : D.G => a*g*a⁻¹*g⁻¹)
  exact ((continuous_const.mul continuous_id).mul continuous_const).mul continuous_inv

theorem native_rational_commutator_character_two_right {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker)
    (a g : D.G) (hg : g ∈ nativeRationalFilteredGroupLayer D L 2) :
    nativeRationalRelativeCommutatorValue D L χ a g=0 := by
  letI := native_rational_filtered_group_normal D L 2
  exact subgroup_real_commutator_normal_right _ (native_rational_original_commutator_mem_two D L) _
    (native_rational_relative_difference_log_character_mul D L χ hχ)
    (native_rational_difference_character_conjugation D L χ hχ) a ⟨g,hg⟩

noncomputable def nativeRationalCommutatorFirstLayerCoefficient {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) (a : D.G)
    (i : NativeRationalFirstLayerIndex D L) : ℝ :=
  nativeRationalRelativeCommutatorValue D L χ a
    (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (nativeRationalFirstLayerRealBasis D L (Sum.inr i)))/(nativeRationalFirstLayerDenominator D L : ℝ)

theorem native_rational_commutator_first_layer_evaluation {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker) (a g : D.G) :
    nativeRationalRelativeCommutatorValue D L χ a g =
      ∑ i : NativeRationalFirstLayerIndex D L,
        nativeRationalCommutatorFirstLayerCoefficient D L χ a i*nativeRationalFirstLayerCoordinates D L g i := by
  obtain ⟨f,hf,_⟩ := native_continuous_character_linearization (I := D.I) D.Γ
    (nativeRationalRelativeCommutatorValue D L χ a)
    (native_rational_commutator_character_continuous D L χ a)
    (native_rational_commutator_character_mul_right D L χ hχ a)
  have hk : L.layer 2 ≤ f.toLinearMap.ker := by
    intro v hv
    have hm : nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v ∈
        nativeRationalFilteredGroupLayer D L 2 := by
      rw [native_rational_filtered_group_logarithm_iff,nativeLieGlobalLogarithm_exponential]
      exact hv
    have he := hf (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v)
    rw [nativeLieGlobalLogarithm_exponential,
      native_rational_commutator_character_two_right D L χ hχ a _ hm] at he
    exact he.symm
  rw [hf g]
  change nativeLieLogarithmCharacter (I := D.I) (G := D.G) f.toLinearMap g = _
  rw [native_rational_first_layer_character_evaluation D L f.toLinearMap hk]
  apply Finset.sum_congr rfl
  intro i _
  have he := hf (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
    (nativeRationalFirstLayerRealBasis D L (Sum.inr i)))
  rw [nativeLieGlobalLogarithm_exponential] at he
  change (f (nativeRationalFirstLayerRealBasis D L (Sum.inr i))/_)*_ = _
  rw [← he]
  rfl

end Hindman168
