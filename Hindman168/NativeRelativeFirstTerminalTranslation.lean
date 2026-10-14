import Hindman168.NativeOriginalTerminalFourierGroupAction
import Hindman168.NativeRelativeInclusion

/-! ACTUAL first-coordinate ORIGINAL terminal translations belong to
SAME relative first group when filtration degree is at least two. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_original_terminal_torus_projection_surjective {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    Function.Surjective (nativeOriginalTerminalTorusProjection D d hd) := by
  intro a
  obtain ⟨z,hz⟩ := native_central_subspace_torus_projection_surjective (I := D.I) D.Γ
    (nativeOriginalTerminalModel D d) (native_original_terminal_model_le_center D d hd)
    (native_original_terminal_model_rational D d) a
  let z0 : roughStretchedLowerCentralFiltration D.G d (s*d) :=
    ⟨z.val,Eq.mp (congrArg (fun K : Subgroup D.G => z.val ∈ K)
      (native_original_terminal_central_subgroup_eq D d hd)) z.property⟩
  refine ⟨z0,?_⟩
  have he : (⟨z0.val,Eq.mpr (congrArg (fun K : Subgroup D.G => z0.val ∈ K)
    (native_original_terminal_central_subgroup_eq D d hd)) z0.property⟩ :
      nativeCentralSubspaceSubgroup (I := D.I) (nativeOriginalTerminalModel D d)
        (native_original_terminal_model_le_center D d hd)) = z := Subtype.ext rfl
  exact (congrArg (nativeCentralSubspaceTorusProjection (I := D.I) D.Γ (nativeOriginalTerminalModel D d)
    (native_original_terminal_model_le_center D d hd) (native_original_terminal_model_rational D d)) he).trans hz

def nativeRelativeFirstTerminalElement {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (d : ℕ) (hd : 0 < d) (hdeg : 2 ≤ s*d)
    (z : roughStretchedLowerCentralFiltration D.G d (s*d)) : (nativeRelativeSquareData D d hd 1).G := by
  refine ⟨((z : D.G),1),?_⟩
  apply (relative_square_filtration_mem_iff _ _ 1 _).mpr
  have h1 : (z : D.G) ∈ roughStretchedLowerCentralFiltration D.G d 1 := by
    rw [rough_stretched_filtration_one d hd]
    exact Subgroup.mem_top _
  refine ⟨h1,Subgroup.one_mem _,?_⟩
  change (1 : D.G)⁻¹*(z : D.G) ∈ roughStretchedLowerCentralFiltration D.G d 2
  rw [inv_one,one_mul]
  exact rough_stretched_filtration_antitone d hd hdeg z.property

theorem native_relative_first_terminal_element_apply {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (d : ℕ) (hd : 0 < d) (hdeg : 2 ≤ s*d)
    (z : roughStretchedLowerCentralFiltration D.G d (s*d)) :
    nativeRelativeGroupInclusion D d hd 1 (nativeRelativeFirstTerminalElement D d hd hdeg z) = ((z : D.G),1) := rfl

end Hindman168
