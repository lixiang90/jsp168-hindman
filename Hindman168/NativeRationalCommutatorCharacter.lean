import Hindman168.NativeRationalDifferenceConjugation

/-! Genuine original commutator pairing of the actual F_2 real character.
Additivity in BOTH original group variables and exact integer-power formula
are derived from actual relative horizontality. -/
namespace Hindman168
open scoped Manifold ContDiff commutatorElement
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalRelativeCommutatorValue {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) (g h : D.G) : ℝ :=
  nativeRationalRelativeDifferenceLogCharacter D L χ
    (subgroupCommElement _ (native_rational_original_commutator_mem_two D L) g h)

theorem native_rational_commutator_character_mul_left {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker) (x y z : D.G) :
    nativeRationalRelativeCommutatorValue D L χ (x*y) z =
      nativeRationalRelativeCommutatorValue D L χ x z+nativeRationalRelativeCommutatorValue D L χ y z := by
  letI := native_rational_filtered_group_normal D L 2
  exact subgroup_real_commutator_mul_left _ (native_rational_original_commutator_mem_two D L) _
    (native_rational_relative_difference_log_character_mul D L χ hχ)
    (native_rational_difference_character_conjugation D L χ hχ) x y z

theorem native_rational_commutator_character_mul_right {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker) (x y z : D.G) :
    nativeRationalRelativeCommutatorValue D L χ x (y*z) =
      nativeRationalRelativeCommutatorValue D L χ x y+nativeRationalRelativeCommutatorValue D L χ x z := by
  letI := native_rational_filtered_group_normal D L 2
  exact subgroup_real_commutator_mul_right _ (native_rational_original_commutator_mem_two D L) _
    (native_rational_relative_difference_log_character_mul D L χ hχ)
    (native_rational_difference_character_conjugation D L χ hχ) x y z

theorem native_rational_commutator_character_zpow {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker) (x y : D.G) (n : ℤ) :
    nativeRationalRelativeCommutatorValue D L χ (x^n) y =
      (n : ℝ)*nativeRationalRelativeCommutatorValue D L χ x y := by
  letI := native_rational_filtered_group_normal D L 2
  exact subgroup_real_commutator_zpow_left _ (native_rational_original_commutator_mem_two D L) _
    (native_rational_relative_difference_log_character_mul D L χ hχ)
    (native_rational_difference_character_conjugation D L χ hχ) x y n

theorem native_rational_commutator_character_lattice {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : ∀ γ ∈ (nativeRationalRelativeData D L 1).Γ, ∃ m : ℤ,
      χ (nativeLieGlobalLogarithm (E := (nativeRationalRelativeData D L 1).E)
        (I := (nativeRationalRelativeData D L 1).I) (G := (nativeRationalRelativeData D L 1).G) γ) = (m : ℝ))
    (g h : D.Γ) : ∃ m : ℤ, nativeRationalRelativeCommutatorValue D L χ g h = (m : ℝ) := by
  apply native_rational_relative_difference_log_character_lattice D L χ hχ
  change ⁅g.val,h.val⁆ ∈ D.Γ
  rw [commutatorElement_def]
  exact D.Γ.mul_mem (D.Γ.mul_mem (D.Γ.mul_mem g.property h.property)
    (D.Γ.inv_mem g.property)) (D.Γ.inv_mem h.property)

end Hindman168
