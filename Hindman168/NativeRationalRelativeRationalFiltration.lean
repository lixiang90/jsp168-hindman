import Hindman168.NativeRationalRelativeLieFiltration
import Hindman168.RationalRealSpanTransport

/-! The actual relative native data of ANY finite rational Lie filtration
again has a fully proved finite rational Lie filtration, without re-stretching. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_relative_inclusion_rational_iff {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (v : (nativeRationalRelativeData D F 1).E) :
    letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
    v ∈ nativeSubgroupRationalLogSpan (E := (nativeRationalRelativeData D F 1).E)
      (I := (nativeRationalRelativeData D F 1).I) (nativeRationalRelativeData D F 1).Γ ↔
    nativeRationalRelativeModelInclusion D F 1 v ∈ nativeSubgroupRationalLogSpan
      (E := D.E × D.E) (I := D.I.prod D.I) (D.Γ.prod D.Γ) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  rw [nativeSubgroupRationalLogSpan_mem_iff_positive_power,
    nativeSubgroupRationalLogSpan_mem_iff_positive_power]
  have he := native_rational_relative_data_exponential D F 1 v
  have hPow : ∀ n : ℕ,
      nativeLieExponential (E := (nativeRationalRelativeData D F 1).E)
        (I := (nativeRationalRelativeData D F 1).I) (G := (nativeRationalRelativeData D F 1).G) v ^ n ∈
          (nativeRationalRelativeData D F 1).Γ ↔
      nativeLieExponential (E := D.E × D.E) (I := D.I.prod D.I) (G := D.G × D.G)
        (nativeRationalRelativeModelInclusion D F 1 v) ^ n ∈ D.Γ.prod D.Γ := by
    intro n
    change nativeRationalRelativeGroupInclusion D F 1
      (nativeLieExponential (E := (nativeRationalRelativeData D F 1).E)
        (I := (nativeRationalRelativeData D F 1).I) (G := (nativeRationalRelativeData D F 1).G) v ^ n) ∈
        D.Γ.prod D.Γ ↔ _
    rw [map_pow,he]
  exact exists_congr (fun n => and_congr_right (fun _ => hPow n))

theorem native_rational_relative_lie_layer_rational {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    nativeLatticeRationalSubspace (E := (nativeRationalRelativeData D F 1).E)
      (I := (nativeRationalRelativeData D F 1).I) (nativeRationalRelativeData D F 1).Γ
        (nativeRationalRelativeLieLayer D F i) := by
  cases i with
  | zero =>
    rw [native_rational_relative_lie_zero D F]
    unfold nativeLatticeRationalSubspace
    simp only [Submodule.restrictScalars_top,top_inf_eq]
    exact nativeSubgroupRationalLogSpan_real_span_eq_top
      (E := (nativeRationalRelativeData D F 1).E)
      (I := (nativeRationalRelativeData D F 1).I) (nativeRationalRelativeData D F 1).Γ
  | succ i =>
    letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
    let L := (nativeRationalRelativeModelInclusion D F 1).toLinearMap
    have hL : Function.Injective L := Subtype.val_injective
    have hRange : relativeLinearFiltration F.layer (i+1) ≤ LinearMap.range L := by
      intro v hv
      have hv1 := (relative_linear_filtration_antitone F.layer F.antitone) (Nat.le_add_left 1 i) hv
      rw [← native_rational_relative_subalgebra_model D F 1] at hv1
      exact ⟨⟨v,hv1⟩,rfl⟩
    exact rational_real_span_comap L hL (relativeLinearFiltration F.layer (i+1)) hRange
      (nativeSubgroupRationalLogSpan (E := (nativeRationalRelativeData D F 1).E)
        (I := (nativeRationalRelativeData D F 1).I) (nativeRationalRelativeData D F 1).Γ)
      (nativeSubgroupRationalLogSpan (E := D.E × D.E) (I := D.I.prod D.I) (D.Γ.prod D.Γ))
      (native_rational_relative_inclusion_rational_iff D F)
      (native_rational_relative_model_rational D F (i+1))

theorem native_rational_relative_lie_terminal {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    nativeRationalRelativeLieLayer D F (ℓ+1) = ⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  change nativeRationalRelativeModelInclusion D F 1 v ∈ relativeLinearFiltration F.layer (ℓ+1) at hv
  have hm := (relative_linear_model_mem_iff _ _ _).mp hv
  have h1 := hm.1
  have h2 := hm.2.1
  rw [F.terminal,Submodule.mem_bot] at h1 h2
  have he : nativeRationalRelativeModelInclusion D F 1 v = 0 := Prod.ext h1 h2
  change v = 0
  exact Subtype.ext he

noncomputable def nativeRelativeRationalLieFiltration {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    NativeRationalLieFiltration (nativeRationalRelativeData D F 1) ℓ where
  layer := nativeRationalRelativeLieLayer D F
  antitone := native_rational_relative_lie_antitone D F
  zero := native_rational_relative_lie_zero D F
  one := native_rational_relative_lie_one D F
  bracket := fun _ _ _ _ hv hw => native_rational_relative_lie_bracket D F hv hw
  rational := native_rational_relative_lie_layer_rational D F
  terminal := native_rational_relative_lie_terminal D F

end Hindman168
