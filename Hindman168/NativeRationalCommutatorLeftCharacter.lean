import Hindman168.NativeRationalCommutatorFirstLayer

/-! Actual first-variable commutator characters: antisymmetry, continuity,
the TRUE F_2 kernel and real Lie linearization, without lattice assumptions. -/
namespace Hindman168
open scoped Manifold ContDiff commutatorElement
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_commutator_character_swap {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker) (g h : D.G) :
    nativeRationalRelativeCommutatorValue D L χ g h =
      -nativeRationalRelativeCommutatorValue D L χ h g := by
  have he : subgroupCommElement _ (native_rational_original_commutator_mem_two D L) g h =
      (subgroupCommElement _ (native_rational_original_commutator_mem_two D L) h g)⁻¹ := by
    apply Subtype.ext
    simp only [subgroupCommElement,Subgroup.coe_inv,commutatorElement_def]
    group
  change nativeRationalRelativeDifferenceLogCharacter D L χ _ = -nativeRationalRelativeDifferenceLogCharacter D L χ _
  rw [he]
  exact subgroup_real_character_inv _ _ (native_rational_relative_difference_log_character_mul D L χ hχ) _

theorem native_rational_commutator_character_continuous_left {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker) (h : D.G) :
    Continuous (fun g => nativeRationalRelativeCommutatorValue D L χ g h) := by
  have he : (fun g => nativeRationalRelativeCommutatorValue D L χ g h) =
      fun g => -nativeRationalRelativeCommutatorValue D L χ h g := by
    funext g
    exact native_rational_commutator_character_swap D L χ hχ g h
  rw [he]
  exact (native_rational_commutator_character_continuous D L χ h).neg

theorem native_rational_commutator_character_two_left {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker)
    (g h : D.G) (hg : g ∈ nativeRationalFilteredGroupLayer D L 2) :
    nativeRationalRelativeCommutatorValue D L χ g h = 0 := by
  rw [native_rational_commutator_character_swap D L χ hχ,
    native_rational_commutator_character_two_right D L χ hχ h g hg,neg_zero]

noncomputable def nativeRationalCommutatorLeftCharacter {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker) (h : D.G) : D.E →L[ℝ] ℝ :=
  Classical.choose (native_continuous_character_linearization (I := D.I) D.Γ
    (fun g => nativeRationalRelativeCommutatorValue D L χ g h)
    (native_rational_commutator_character_continuous_left D L χ hχ h)
    (fun g g' => native_rational_commutator_character_mul_left D L χ hχ g g' h))

theorem native_rational_commutator_left_character_evaluation {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker) (g h : D.G) :
    nativeRationalCommutatorLeftCharacter D L χ hχ h
      (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g) =
        nativeRationalRelativeCommutatorValue D L χ g h :=
  ((Classical.choose_spec (native_continuous_character_linearization (I := D.I) D.Γ
    (fun g => nativeRationalRelativeCommutatorValue D L χ g h)
    (native_rational_commutator_character_continuous_left D L χ hχ h)
    (fun g g' => native_rational_commutator_character_mul_left D L χ hχ g g' h))).1 g).symm

theorem native_rational_commutator_left_character_kills_two {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker) (h : D.G) :
    L.layer 2 ≤ (nativeRationalCommutatorLeftCharacter D L χ hχ h).toLinearMap.ker := by
  intro v hv
  have hm : nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v ∈ nativeRationalFilteredGroupLayer D L 2 := by
    rw [native_rational_filtered_group_logarithm_iff,nativeLieGlobalLogarithm_exponential]
    exact hv
  have he := native_rational_commutator_left_character_evaluation D L χ hχ
    (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v) h
  rw [nativeLieGlobalLogarithm_exponential,native_rational_commutator_character_two_left D L χ hχ _ h hm] at he
  exact he

end Hindman168
