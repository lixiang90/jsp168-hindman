import Hindman168.NativeRationalRelativeDifferenceCharacter
import Hindman168.SubgroupRealCharacterConjugation

/-! Actual F_2 character is invariant under conjugation by the ENTIRE
original group, proved by genuine relative diagonal conjugation. -/
namespace Hindman168
open scoped Manifold ContDiff commutatorElement
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_relative_first_difference_conjugation {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    letI := native_rational_filtered_group_normal D L 2
    ∀ (g : D.G) (w : nativeRationalFilteredGroupLayer D L 2),
    nativeRationalRelativeFirstDifferenceGroup D L (subgroupConjugate _ g w) =
      nativeRationalRelativeDiagonalGroup D L g * nativeRationalRelativeFirstDifferenceGroup D L w *
        (nativeRationalRelativeDiagonalGroup D L g)⁻¹ := by
  letI := native_rational_filtered_group_normal D L 2
  intro g w
  apply Subtype.ext
  change (g*w.val*g⁻¹,1) = (g*w.val*g⁻¹,g*1*g⁻¹)
  simp only [mul_one,mul_inv_cancel]

theorem native_rational_difference_character_conjugation {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker) :
    letI := native_rational_filtered_group_normal D L 2
    ∀ (g : D.G) (w : nativeRationalFilteredGroupLayer D L 2),
    nativeRationalRelativeDifferenceLogCharacter D L χ (subgroupConjugate _ g w) =
      nativeRationalRelativeDifferenceLogCharacter D L χ w := by
  letI := native_rational_filtered_group_normal D L 2
  intro g w
  let Ψ := nativeLieLogarithmCharacter (I := (nativeRationalRelativeData D L 1).I)
    (G := (nativeRationalRelativeData D L 1).G) χ.toLinearMap
  have hm : ∀ x y, Ψ (x*y) = Ψ x+Ψ y := nativeLieLogarithmCharacter_mul χ.toLinearMap hχ
  have he := hm (nativeRationalRelativeDiagonalGroup D L g)
    (nativeRationalRelativeDiagonalGroup D L g)⁻¹
  have hz : Ψ 1 = 0 := by
    change χ (nativeLieGlobalLogarithm (E := (nativeRationalRelativeData D L 1).E)
      (I := (nativeRationalRelativeData D L 1).I) (G := (nativeRationalRelativeData D L 1).G) 1) = 0
    rw [nativeLieGlobalLogarithm_one,map_zero]
  rw [mul_inv_cancel,hz] at he
  change Ψ (nativeRationalRelativeFirstDifferenceGroup D L (subgroupConjugate _ g w)) =
    Ψ (nativeRationalRelativeFirstDifferenceGroup D L w)
  rw [native_rational_relative_first_difference_conjugation,hm,hm]
  linarith

theorem native_rational_original_commutator_mem_two {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (g h : D.G) :
    ⁅g,h⁆ ∈ nativeRationalFilteredGroupLayer D L 2 := by
  apply (native_rational_filtered_group_conditions D L).commutator_mem 1 1
  · rw [native_rational_filtered_group_one]; exact Subgroup.mem_top _
  · rw [native_rational_filtered_group_one]; exact Subgroup.mem_top _

end Hindman168
