import Hindman168.NativeRationalTerminalRationalSpan
import Hindman168.NativeRationalTerminalProjectionKernel
import Hindman168.NativeSmoothHomLieBracket
import Hindman168.RationalRealSpanTransport

/-! Actual Lie/group image layers on the true native terminal quotient.
All rationality, bracket and degree-drop inputs are proved from original data. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalTerminalImageLieLayer {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    Submodule ℝ (nativeRationalTerminalQuotientData D F).E :=
  (F.layer i).map (nativeRationalTerminalModelProjection D F).toLinearMap

noncomputable def nativeRationalTerminalImageGroupLayer {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    Subgroup (nativeRationalTerminalQuotientData D F).G :=
  (nativeRationalFilteredGroupLayer D F i).map (nativeRationalTerminalGroupProjection D F)

theorem native_rational_terminal_image_lie_antitone {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    Antitone (nativeRationalTerminalImageLieLayer D F) := by
  intro i j hij
  exact Submodule.map_mono (F.antitone hij)

theorem native_rational_terminal_image_lie_zero {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    nativeRationalTerminalImageLieLayer D F 0 = ⊤ := by
  rw [nativeRationalTerminalImageLieLayer,F.zero,Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (native_rational_terminal_model_projection_surjective D F)

theorem native_rational_terminal_image_lie_one {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    nativeRationalTerminalImageLieLayer D F 1 = ⊤ := by
  rw [nativeRationalTerminalImageLieLayer,F.one,Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (native_rational_terminal_model_projection_surjective D F)

theorem native_rational_terminal_image_logarithm_iff {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ)
    (g : (nativeRationalTerminalQuotientData D F).G) :
    g ∈ nativeRationalTerminalImageGroupLayer D F i ↔
      nativeLieGlobalLogarithm (E := (nativeRationalTerminalQuotientData D F).E)
        (I := (nativeRationalTerminalQuotientData D F).I) (G := (nativeRationalTerminalQuotientData D F).G) g ∈
          nativeRationalTerminalImageLieLayer D F i := by
  constructor
  · rintro ⟨a,ha,rfl⟩
    rw [native_rational_terminal_data_logarithm]
    exact Submodule.mem_map_of_mem ((native_rational_filtered_group_logarithm_iff D F i a).mp ha)
  · rintro ⟨v,hv,he⟩
    refine ⟨nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v,?_,?_⟩
    · exact ⟨v,hv,rfl⟩
    · rw [native_rational_terminal_data_exponential]
      exact (congrArg (nativeLieExponential (E := (nativeRationalTerminalQuotientData D F).E)
        (I := (nativeRationalTerminalQuotientData D F).I) (G := (nativeRationalTerminalQuotientData D F).G)) he).trans
          (nativeLieExponential_globalLogarithm (E := (nativeRationalTerminalQuotientData D F).E)
            (I := (nativeRationalTerminalQuotientData D F).I) (G := (nativeRationalTerminalQuotientData D F).G) g)

theorem native_rational_terminal_image_lie_bracket {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    {i j : ℕ} {v w : (nativeRationalTerminalQuotientData D F).E}
    (hv : v ∈ nativeRationalTerminalImageLieLayer D F i) (hw : w ∈ nativeRationalTerminalImageLieLayer D F j) :
    nativeLieAdjointDifferential (I := (nativeRationalTerminalQuotientData D F).I)
      (G := (nativeRationalTerminalQuotientData D F).G) v w ∈ nativeRationalTerminalImageLieLayer D F (i+j) := by
  obtain ⟨a,ha,rfl⟩ := hv
  obtain ⟨b,hb,rfl⟩ := hw
  have he := nativeSmoothHom_generator_intertwine (E := D.E) (F := (nativeRationalTerminalQuotientData D F).E)
    (I := D.I) (J := (nativeRationalTerminalQuotientData D F).I)
    (nativeRationalTerminalGroupProjection D F) (native_rational_terminal_projection_contMDiff D F) a b
  rw [native_rational_terminal_projection_mfderiv] at he
  simp only [nativeLieAdjointGenerator_eq_differential] at he
  exact he ▸ (Submodule.mem_map_of_mem (F.bracket i j a b ha hb))

theorem native_rational_terminal_image_lie_rational {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    nativeLatticeRationalSubspace (E := (nativeRationalTerminalQuotientData D F).E)
      (I := (nativeRationalTerminalQuotientData D F).I) (nativeRationalTerminalQuotientData D F).Γ
        (nativeRationalTerminalImageLieLayer D F i) :=
  rational_real_span_map (nativeRationalTerminalModelProjection D F).toLinearMap (F.layer i)
    (nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ)
    (nativeSubgroupRationalLogSpan (E := (nativeRationalTerminalQuotientData D F).E)
      (I := (nativeRationalTerminalQuotientData D F).I) (nativeRationalTerminalQuotientData D F).Γ)
    (fun _ hv => native_rational_terminal_rational_mem D F hv) (F.rational i)

theorem native_rational_terminal_image_lie_terminal {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) (hi : ℓ ≤ i) :
    nativeRationalTerminalImageLieLayer D F i = ⊥ := by
  apply le_antisymm _ bot_le
  rintro v ⟨a,ha,rfl⟩
  change nativeRationalTerminalModelProjection D F a = 0
  exact (native_rational_terminal_model_projection_zero_iff D F a).mpr (F.antitone hi ha)

noncomputable def nativeTerminalRationalLieFiltration {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    NativeRationalLieFiltration (nativeRationalTerminalQuotientData D F) (ℓ-1) where
  layer := nativeRationalTerminalImageLieLayer D F
  antitone := native_rational_terminal_image_lie_antitone D F
  zero := native_rational_terminal_image_lie_zero D F
  one := native_rational_terminal_image_lie_one D F
  bracket := fun _ _ _ _ hv hw => native_rational_terminal_image_lie_bracket D F hv hw
  rational := native_rational_terminal_image_lie_rational D F
  terminal := native_rational_terminal_image_lie_terminal D F _ (by omega)

end Hindman168
