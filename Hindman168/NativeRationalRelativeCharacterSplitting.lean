import Hindman168.NativeRationalRelativeDiagonalGeometry
import Hindman168.NativeContinuousHorizontalCharacter

/-! Genuine diagonal/difference splitting of an actual relative character.
Nonzeroness on the diagonal is not inferred from relative nonzeroness. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalRelativeDiagonalCharacter {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) : D.E →L[ℝ] ℝ :=
  χ.comp (nativeRationalRelativeDiagonalModel D L)

noncomputable def nativeRationalRelativeDifferenceCharacter {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) : (L.layer 2) →L[ℝ] ℝ :=
  χ.comp (nativeRationalRelativeFirstDifferenceModel D L)

theorem native_rational_relative_character_decomposition {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (v : (nativeRationalRelativeData D L 1).E) :
    χ v = nativeRationalRelativeDiagonalCharacter D L χ v.val.2 +
      nativeRationalRelativeDifferenceCharacter D L χ (nativeRationalRelativeDifferenceCoordinate D L v) := by
  have he := congrArg χ (native_rational_relative_model_decomposition D L v)
  exact he.trans (map_add χ _ _)

theorem native_rational_relative_character_nonzero_alternative {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) (hχ : χ ≠ 0) :
    nativeRationalRelativeDiagonalCharacter D L χ ≠ 0 ∨
      nativeRationalRelativeDifferenceCharacter D L χ ≠ 0 := by
  by_contra h
  push Not at h
  apply hχ
  ext v
  rw [native_rational_relative_character_decomposition,h.1,h.2]
  simp only [zero_apply,add_zero]

theorem native_rational_relative_diagonal_character_log {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) (g : D.G) :
    nativeLieLogarithmCharacter (I := D.I) (G := D.G)
      (nativeRationalRelativeDiagonalCharacter D L χ).toLinearMap g =
    nativeLieLogarithmCharacter (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) χ.toLinearMap (nativeRationalRelativeDiagonalGroup D L g) := by
  change χ (nativeRationalRelativeDiagonalModel D L
    (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g)) = _
  rw [← native_rational_relative_diagonal_logarithm]
  rfl

theorem native_rational_relative_diagonal_character_mul {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker) (g h : D.G) :
    nativeLieLogarithmCharacter (I := D.I) (G := D.G)
      (nativeRationalRelativeDiagonalCharacter D L χ).toLinearMap (g*h) =
    nativeLieLogarithmCharacter (I := D.I) (G := D.G)
      (nativeRationalRelativeDiagonalCharacter D L χ).toLinearMap g +
    nativeLieLogarithmCharacter (I := D.I) (G := D.G)
      (nativeRationalRelativeDiagonalCharacter D L χ).toLinearMap h := by
  rw [native_rational_relative_diagonal_character_log,native_rational_relative_diagonal_character_log,
    native_rational_relative_diagonal_character_log,map_mul]
  exact nativeLieLogarithmCharacter_mul (I := (nativeRationalRelativeData D L 1).I)
    (G := (nativeRationalRelativeData D L 1).G) χ.toLinearMap hχ _ _

theorem native_rational_relative_diagonal_character_commutator {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker) :
    nativeLieLowerCentralModel (I := D.I) (G := D.G) 1 ≤
      (nativeRationalRelativeDiagonalCharacter D L χ).toLinearMap.ker :=
  native_continuous_character_linearization_horizontal (I := D.I)
    (nativeLieLogarithmCharacter (I := D.I) (G := D.G) (nativeRationalRelativeDiagonalCharacter D L χ).toLinearMap)
    (native_rational_relative_diagonal_character_mul D L χ hχ) (nativeRationalRelativeDiagonalCharacter D L χ)
    (fun _ => rfl)

theorem native_rational_relative_diagonal_character_lattice {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : ∀ γ ∈ (nativeRationalRelativeData D L 1).Γ, ∃ m : ℤ,
      χ (nativeLieGlobalLogarithm (E := (nativeRationalRelativeData D L 1).E)
        (I := (nativeRationalRelativeData D L 1).I) (G := (nativeRationalRelativeData D L 1).G) γ) = (m : ℝ)) :
    ∀ γ ∈ D.Γ, ∃ m : ℤ, nativeRationalRelativeDiagonalCharacter D L χ
      (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) γ) = (m : ℝ) := by
  intro γ hγ
  obtain ⟨m,he⟩ := hχ _ (native_rational_relative_diagonal_lattice D L γ hγ)
  rw [native_rational_relative_diagonal_logarithm] at he
  exact ⟨m,he⟩

theorem native_rational_relative_diagonal_character_horizontal {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : RoughNativeHorizontalFunctional (I := (nativeRationalRelativeData D L 1).I)
      (nativeRationalRelativeData D L 1).Γ χ.toLinearMap)
    (hne : nativeRationalRelativeDiagonalCharacter D L χ ≠ 0) :
    RoughNativeHorizontalFunctional (I := D.I) D.Γ
      (nativeRationalRelativeDiagonalCharacter D L χ).toLinearMap := by
  refine ⟨?_,native_rational_relative_diagonal_character_commutator D L χ hχ.2.1,
    native_rational_relative_diagonal_character_lattice D L χ hχ.2.2⟩
  intro hz
  apply hne
  ext v
  exact DFunLike.congr_fun hz v

end Hindman168
