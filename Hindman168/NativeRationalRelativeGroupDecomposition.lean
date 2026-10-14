import Hindman168.NativeRationalDifferenceConjugation

/-! Exact original-group diagonal/difference decomposition of ACTUAL relative
group elements and their genuine real characters. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_relative_first_difference_mem {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (g : (nativeRationalRelativeData D L 1).G) :
    g.val.1*g.val.2⁻¹ ∈ nativeRationalFilteredGroupLayer D L 2 := by
  letI := native_rational_filtered_group_normal D L 2
  have hm := ((relative_square_filtration_mem_iff _ _ 1 _).mp g.property).2.2
  have hc := (inferInstance : (nativeRationalFilteredGroupLayer D L 2).Normal).conj_mem
    (g.val.2⁻¹*g.val.1) hm g.val.2
  simpa only [mul_inv_cancel_left] using hc

def nativeRationalRelativeGroupDifference {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (g : (nativeRationalRelativeData D L 1).G) : nativeRationalFilteredGroupLayer D L 2 :=
  ⟨g.val.1*g.val.2⁻¹,native_rational_relative_first_difference_mem D L g⟩

theorem native_rational_relative_group_decomposition {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (g : (nativeRationalRelativeData D L 1).G) :
    g = nativeRationalRelativeFirstDifferenceGroup D L (nativeRationalRelativeGroupDifference D L g) *
      nativeRationalRelativeDiagonalGroup D L g.val.2 := by
  apply Subtype.ext
  change g.val = ((g.val.1*g.val.2⁻¹)*g.val.2,1*g.val.2)
  simp only [inv_mul_cancel_right,one_mul]

theorem native_rational_relative_group_character_decomposition {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker)
    (g : (nativeRationalRelativeData D L 1).G) :
    nativeLieLogarithmCharacter (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) χ.toLinearMap g =
      nativeLieLogarithmCharacter (I := D.I) (G := D.G)
        (nativeRationalRelativeDiagonalCharacter D L χ).toLinearMap g.val.2 +
      nativeRationalRelativeDifferenceLogCharacter D L χ (nativeRationalRelativeGroupDifference D L g) := by
  conv_lhs => rw [native_rational_relative_group_decomposition D L g]
  rw [nativeLieLogarithmCharacter_mul χ.toLinearMap hχ,
    ← native_rational_relative_diagonal_character_log]
  exact add_comm _ _

end Hindman168
