import Hindman168.NativeRationalRelativeCharacterSplitting

/-! The actual F_2 component is a genuine continuous additive character
on the original F_2 subgroup, integral on its actual restricted lattice.
No extension of this character to the whole original group is asserted. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

def nativeRationalRelativeFirstDifferenceGroup {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    nativeRationalFilteredGroupLayer D L 2 →* (nativeRationalRelativeData D L 1).G where
  toFun g := ⟨(g.val,1),by
    apply (relative_square_filtration_mem_iff _ _ 1 _).mpr
    rw [native_rational_filtered_group_one]
    exact ⟨Subgroup.mem_top _,Subgroup.mem_top _,by simpa only [inv_one,one_mul] using g.property⟩⟩
  map_one' := Subtype.ext rfl
  map_mul' g h := Subtype.ext (by
    change (g.val*h.val,1) = (g.val*h.val,(1 : D.G)*1)
    rw [one_mul])

theorem native_rational_relative_first_difference_logarithm {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (g : nativeRationalFilteredGroupLayer D L 2) :
    nativeLieGlobalLogarithm (E := (nativeRationalRelativeData D L 1).E)
      (I := (nativeRationalRelativeData D L 1).I) (G := (nativeRationalRelativeData D L 1).G)
        (nativeRationalRelativeFirstDifferenceGroup D L g) =
    nativeRationalRelativeFirstDifferenceModel D L
      ⟨nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g.val,
        (native_rational_filtered_group_logarithm_iff D L 2 g.val).mp g.property⟩ := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  apply Subtype.ext
  have he := native_rational_relative_data_logarithm D L 1 (nativeRationalRelativeFirstDifferenceGroup D L g)
  rw [nativeProductGlobalLogarithm_eq] at he
  change _ = (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g.val,
    nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) 1) at he
  rw [nativeLieGlobalLogarithm_one] at he
  exact he

noncomputable def nativeRationalRelativeDifferenceLogCharacter {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) :
    C(nativeRationalFilteredGroupLayer D L 2,ℝ) :=
  (nativeLieLogarithmCharacter (I := (nativeRationalRelativeData D L 1).I)
    (G := (nativeRationalRelativeData D L 1).G) χ.toLinearMap).comp
      ⟨nativeRationalRelativeFirstDifferenceGroup D L,
        (continuous_subtype_val.prodMk continuous_const).subtype_mk _⟩

theorem native_rational_relative_difference_log_character_apply {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) (g : nativeRationalFilteredGroupLayer D L 2) :
    nativeRationalRelativeDifferenceLogCharacter D L χ g =
      nativeRationalRelativeDifferenceCharacter D L χ
        ⟨nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g.val,
          (native_rational_filtered_group_logarithm_iff D L 2 g.val).mp g.property⟩ := by
  change χ (nativeLieGlobalLogarithm (E := (nativeRationalRelativeData D L 1).E)
    (I := (nativeRationalRelativeData D L 1).I) (G := (nativeRationalRelativeData D L 1).G)
      (nativeRationalRelativeFirstDifferenceGroup D L g)) = _
  rw [native_rational_relative_first_difference_logarithm]
  rfl

theorem native_rational_relative_difference_log_character_mul {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker)
    (g h : nativeRationalFilteredGroupLayer D L 2) :
    nativeRationalRelativeDifferenceLogCharacter D L χ (g*h) =
      nativeRationalRelativeDifferenceLogCharacter D L χ g + nativeRationalRelativeDifferenceLogCharacter D L χ h := by
  change nativeLieLogarithmCharacter (I := (nativeRationalRelativeData D L 1).I)
    (G := (nativeRationalRelativeData D L 1).G) χ.toLinearMap (nativeRationalRelativeFirstDifferenceGroup D L (g*h)) = _
  rw [map_mul]
  exact nativeLieLogarithmCharacter_mul (I := (nativeRationalRelativeData D L 1).I)
    (G := (nativeRationalRelativeData D L 1).G) χ.toLinearMap hχ _ _

theorem native_rational_relative_difference_log_character_lattice {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : ∀ γ ∈ (nativeRationalRelativeData D L 1).Γ, ∃ m : ℤ,
      χ (nativeLieGlobalLogarithm (E := (nativeRationalRelativeData D L 1).E)
        (I := (nativeRationalRelativeData D L 1).I) (G := (nativeRationalRelativeData D L 1).G) γ) = (m : ℝ))
    (g : nativeRationalFilteredGroupLayer D L 2) (hg : g.val ∈ D.Γ) :
    ∃ m : ℤ, nativeRationalRelativeDifferenceLogCharacter D L χ g = (m : ℝ) := by
  have hm : nativeRationalRelativeFirstDifferenceGroup D L g ∈ (nativeRationalRelativeData D L 1).Γ :=
    ⟨hg,D.Γ.one_mem⟩
  exact hχ _ hm

theorem native_rational_relative_difference_log_character_nonzero {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hne : nativeRationalRelativeDifferenceCharacter D L χ ≠ 0) :
    nativeRationalRelativeDifferenceLogCharacter D L χ ≠ 0 := by
  intro hz
  apply hne
  ext v
  let g : nativeRationalFilteredGroupLayer D L 2 :=
    ⟨nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v.val,by
      apply (native_rational_filtered_group_logarithm_iff D L 2 _).mpr
      rw [nativeLieGlobalLogarithm_exponential]
      exact v.property⟩
  have he := congrArg (fun F : C(nativeRationalFilteredGroupLayer D L 2,ℝ) => F g) hz
  rw [native_rational_relative_difference_log_character_apply] at he
  have hv : (⟨nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g.val,
      (native_rational_filtered_group_logarithm_iff D L 2 g.val).mp g.property⟩ : L.layer 2) = v := by
    apply Subtype.ext
    exact nativeLieGlobalLogarithm_exponential (E := D.E) (I := D.I) (G := D.G) v.val
  rw [hv] at he
  exact he

end Hindman168
