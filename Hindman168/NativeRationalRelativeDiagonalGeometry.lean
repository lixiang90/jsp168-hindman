import Hindman168.NativeRationalRelativeTerminalGeometry
import Hindman168.NativeProductGlobalLogarithm

/-! Actual diagonal and first-difference directions of the relative group/model.
The first-difference model is the true F_2, not all of the original model. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u

noncomputable def nativeRationalRelativeDiagonalModel {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    D.E →L[ℝ] (nativeRationalRelativeData D L 1).E where
  toFun v := ⟨(v,v),by
    rw [native_rational_relative_subalgebra_model]
    apply (relative_linear_model_mem_iff _ _ _).mpr
    rw [L.one]
    exact ⟨Submodule.mem_top,Submodule.mem_top,by simp only [sub_self]; exact Submodule.zero_mem _⟩⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl
  cont := (continuous_id.prodMk continuous_id).subtype_mk _

noncomputable def nativeRationalRelativeFirstDifferenceModel {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    (L.layer 2) →L[ℝ] (nativeRationalRelativeData D L 1).E where
  toFun v := ⟨(v.val,0),by
    rw [native_rational_relative_subalgebra_model]
    apply (relative_linear_model_mem_iff _ _ _).mpr
    rw [L.one]
    exact ⟨Submodule.mem_top,Submodule.mem_top,by simpa only [sub_zero] using v.property⟩⟩
  map_add' v w := Subtype.ext (by
    change (v.val+w.val,0) = (v.val+w.val,0+0)
    rw [add_zero])
  map_smul' c v := Subtype.ext (by
    change (c • v.val,0) = (c • v.val,c • (0 : D.E))
    rw [smul_zero])
  cont := (continuous_subtype_val.prodMk continuous_const).subtype_mk _

noncomputable def nativeRationalRelativeDifferenceCoordinate {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    (nativeRationalRelativeData D L 1).E →L[ℝ] (L.layer 2) where
  toFun v := ⟨v.val.1-v.val.2,by
    have hv := Eq.mp (congrArg (fun T : Submodule ℝ (D.E × D.E) =>
      nativeRationalRelativeModelInclusion D L 1 v ∈ T)
      (native_rational_relative_subalgebra_model D L 1)) v.property
    exact ((relative_linear_model_mem_iff _ _ _).mp hv).2.2⟩
  map_add' v w := Subtype.ext (by
    change (v.val.1+w.val.1)-(v.val.2+w.val.2) = (v.val.1-v.val.2)+(w.val.1-w.val.2)
    abel)
  map_smul' c v := Subtype.ext (by
    change c • v.val.1-c • v.val.2 = c • (v.val.1-v.val.2)
    rw [smul_sub])
  cont := (continuous_subtype_val.fst.sub continuous_subtype_val.snd).subtype_mk _

theorem native_rational_relative_model_decomposition {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (v : (nativeRationalRelativeData D L 1).E) :
    v = nativeRationalRelativeDiagonalModel D L v.val.2 +
      nativeRationalRelativeFirstDifferenceModel D L (nativeRationalRelativeDifferenceCoordinate D L v) := by
  apply Subtype.ext
  change v.val = (v.val.2+(v.val.1-v.val.2),v.val.2+0)
  exact Prod.ext (by symm; rw [add_comm,sub_add_cancel]) (add_zero _).symm

def nativeRationalRelativeDiagonalGroup {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    D.G →* (nativeRationalRelativeData D L 1).G where
  toFun g := ⟨(g,g),by
    apply (relative_square_filtration_mem_iff _ _ 1 _).mpr
    rw [native_rational_filtered_group_one]
    exact ⟨Subgroup.mem_top _,Subgroup.mem_top _,by simp only [inv_mul_cancel]; exact Subgroup.one_mem _⟩⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

theorem native_rational_relative_diagonal_logarithm {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (g : D.G) :
    nativeLieGlobalLogarithm (E := (nativeRationalRelativeData D L 1).E)
      (I := (nativeRationalRelativeData D L 1).I) (G := (nativeRationalRelativeData D L 1).G)
        (nativeRationalRelativeDiagonalGroup D L g) =
      nativeRationalRelativeDiagonalModel D L
        (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  apply Subtype.ext
  have he := native_rational_relative_data_logarithm D L 1 (nativeRationalRelativeDiagonalGroup D L g)
  rw [nativeProductGlobalLogarithm_eq] at he
  exact he

theorem native_rational_relative_diagonal_lattice {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (g : D.G) (hg : g ∈ D.Γ) :
    nativeRationalRelativeDiagonalGroup D L g ∈ (nativeRationalRelativeData D L 1).Γ := by
  exact ⟨hg,hg⟩

end Hindman168
