import Hindman168.NativeRationalRelativeRationalFiltration
import Hindman168.NativeRationalTerminalFourierGroupAction

/-! Actual internal relative terminal layer and first-coordinate translations
for any finite rational filtration. No image filtration is re-stretched. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_relative_group_layer_eq {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    nativeRationalFilteredGroupLayer (nativeRationalRelativeData D L 1)
      (nativeRelativeRationalLieFiltration D L) i = nativeRationalRelativeInternalGroupLayer D L i := by
  ext g
  exact (native_rational_filtered_group_logarithm_iff _ _ i g).trans
    (native_rational_relative_internal_logarithm_iff D L i g).symm

theorem native_rational_relative_terminal_subgroup_eq {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    nativeRationalTerminalSubgroup (nativeRationalRelativeData D L 1)
      (nativeRelativeRationalLieFiltration D L) = nativeRationalRelativeInternalGroupLayer D L ℓ := by
  rw [native_rational_terminal_subgroup_eq,native_rational_relative_group_layer_eq]

theorem native_rational_terminal_group_le_center {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    nativeRationalFilteredGroupLayer D L ℓ ≤ Subgroup.center D.G := by
  rw [← native_rational_terminal_subgroup_eq]
  exact nativeCentralSubspaceSubgroup_le_center _ _

theorem native_rational_terminal_torus_projection_surjective {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    Function.Surjective (nativeRationalTerminalTorusProjection D L) := by
  intro a
  obtain ⟨z,hz⟩ := native_central_subspace_torus_projection_surjective (I := D.I) D.Γ
    (L.layer ℓ) (native_rational_filtered_terminal_central D L) (L.rational ℓ) a
  let z0 : nativeRationalFilteredGroupLayer D L ℓ :=
    ⟨z.val,Eq.mp (congrArg (fun K : Subgroup D.G => z.val ∈ K)
      (native_rational_terminal_subgroup_eq D L)) z.property⟩
  refine ⟨z0,?_⟩
  have he : (⟨z0.val,Eq.mpr (congrArg (fun K : Subgroup D.G => z0.val ∈ K)
    (native_rational_terminal_subgroup_eq D L)) z0.property⟩ :
      nativeRationalTerminalSubgroup D L) = z := Subtype.ext rfl
  exact (congrArg (nativeCentralSubspaceTorusProjection (I := D.I) D.Γ (L.layer ℓ)
    (native_rational_filtered_terminal_central D L) (L.rational ℓ)) he).trans hz

def nativeRationalRelativeFirstTerminalElement {s ℓ : ℕ} (D : NativeNilmanifoldData.{u} s)
    (L : NativeRationalLieFiltration D ℓ) (hdeg : 2 ≤ ℓ)
    (z : nativeRationalFilteredGroupLayer D L ℓ) : (nativeRationalRelativeData D L 1).G := by
  refine ⟨((z : D.G),1),?_⟩
  apply (relative_square_filtration_mem_iff _ _ 1 _).mpr
  have h1 : (z : D.G) ∈ nativeRationalFilteredGroupLayer D L 1 := by
    rw [native_rational_filtered_group_one]; exact Subgroup.mem_top _
  refine ⟨h1,Subgroup.one_mem _,?_⟩
  change (1 : D.G)⁻¹*(z : D.G) ∈ nativeRationalFilteredGroupLayer D L 2
  rw [inv_one,one_mul]
  exact native_rational_filtered_group_antitone D L hdeg z.property

theorem native_rational_relative_first_terminal_element_apply {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (hdeg : 2 ≤ ℓ)
    (z : nativeRationalFilteredGroupLayer D L ℓ) :
    nativeRationalRelativeGroupInclusion D L 1 (nativeRationalRelativeFirstTerminalElement D L hdeg z) =
      ((z : D.G),1) := rfl

end Hindman168
