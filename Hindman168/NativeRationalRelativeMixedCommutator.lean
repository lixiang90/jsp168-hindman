import Hindman168.NativeRationalRelativeCharacterSplitting

/-! The genuine relative horizontal difference component annihilates the
actual original mixed bracket [G,F_2]. This does not imply that it extends
to an original horizontal character killing all of [G,G]. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_relative_mixed_bracket_mem {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (v : D.E) (w : L.layer 2) :
    nativeLieAdjointDifferential (I := D.I) (G := D.G) v w.val ∈ L.layer 2 := by
  have hv : v ∈ L.layer 1 := by rw [L.one]; exact Submodule.mem_top
  exact L.antitone (by omega) (L.bracket 1 2 v w.val hv w.property)

theorem native_rational_relative_mixed_bracket {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (v : D.E) (w : L.layer 2) :
    nativeLieAdjointDifferential (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G)
        (nativeRationalRelativeDiagonalModel D L v) (nativeRationalRelativeFirstDifferenceModel D L w) =
    nativeRationalRelativeFirstDifferenceModel D L
      ⟨nativeLieAdjointDifferential (I := D.I) (G := D.G) v w.val,
        native_rational_relative_mixed_bracket_mem D L v w⟩ := by
  apply Subtype.ext
  have he := native_rational_relative_adjoint_differential D L
    (nativeRationalRelativeDiagonalModel D L v) (nativeRationalRelativeFirstDifferenceModel D L w)
  rw [native_product_adjoint_differential] at he
  change _ = (nativeLieAdjointDifferential (I := D.I) (G := D.G) v w.val,
    nativeLieAdjointDifferential (I := D.I) (G := D.G) v 0) at he
  rw [map_zero] at he
  exact he

theorem native_rational_relative_difference_character_mixed_commutator {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker)
    (v : D.E) (w : L.layer 2) :
    nativeRationalRelativeDifferenceCharacter D L χ
      ⟨nativeLieAdjointDifferential (I := D.I) (G := D.G) v w.val,
        native_rational_relative_mixed_bracket_mem D L v w⟩ = 0 := by
  have hmem := nativeLieAdjointGenerator_mem_lowerCentral_next
    (I := (nativeRationalRelativeData D L 1).I) (G := (nativeRationalRelativeData D L 1).G)
    (nativeRationalRelativeDiagonalModel D L v) (j := 0)
    (w := nativeRationalRelativeFirstDifferenceModel D L w) (by
      rw [nativeLieLowerCentralModel_zero]
      exact Submodule.mem_top)
  rw [nativeLieAdjointGenerator_eq_differential] at hmem
  have hz := hχ hmem
  change χ (nativeLieAdjointDifferential (I := (nativeRationalRelativeData D L 1).I)
    (G := (nativeRationalRelativeData D L 1).G)
      (nativeRationalRelativeDiagonalModel D L v) (nativeRationalRelativeFirstDifferenceModel D L w)) = 0 at hz
  rw [native_rational_relative_mixed_bracket] at hz
  exact hz

end Hindman168
