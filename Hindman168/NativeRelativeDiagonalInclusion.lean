import Hindman168.NativeRelativeTerminalCenter

/-! ACTUAL diagonal inclusion from original model into ACTUAL relative
native model. Its original terminal layer spans ENTIRE terminal subspace. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_relative_base_diagonal_mem {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (d : ℕ) (hd : 0 < d) (v : D.E) :
    (v,v) ∈ nativeLieSubalgebraModel (nativeRelativeSquareNativeLieAlgebra D d 1) := by
  have hi : (1 ⌈/⌉ d)-1 = 0 := by rw [rough_ceiling_index_one d hd,Nat.sub_self]
  have ha : v ∈ nativeLieLowerCentralModel (I := D.I) (G := D.G) ((1 ⌈/⌉ d)-1) := by
    rw [hi,nativeLieLowerCentralModel_zero]
    exact Submodule.mem_top
  have hm := (native_relative_square_model_mem_iff D d 1 (v,v)).mpr
    ⟨ha,ha,by rw [sub_self]; exact Submodule.zero_mem _⟩
  exact Eq.mpr (congrArg (fun V : Submodule ℝ (D.E × D.E) => (v,v) ∈ V)
    (native_relative_square_native_model_eq D d 1)) hm

noncomputable def nativeRelativeDiagonalInclusion {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (d : ℕ) (hd : 0 < d) : D.E →L[ℝ] (nativeRelativeSquareData D d hd 1).E :=
  (show D.E →ₗ[ℝ] (nativeRelativeSquareData D d hd 1).E from {
    toFun := fun v => ⟨(v,v),native_relative_base_diagonal_mem D d hd v⟩
    map_add' := fun _ _ => Subtype.ext rfl
    map_smul' := fun _ _ => Subtype.ext rfl }).toContinuousLinearMap

theorem native_relative_diagonal_inclusion_apply {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (d : ℕ) (hd : 0 < d) (v : D.E) :
    nativeRelativeModelInclusion D d hd 1 (nativeRelativeDiagonalInclusion D d hd v) = (v,v) := rfl

theorem native_relative_terminal_model_eq_map {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (d : ℕ) (hd : 0 < d) :
    nativeRelativeTerminalModel D d hd =
      (nativeLieLowerCentralModel (I := D.I) (G := D.G) (((s*d) ⌈/⌉ d)-1)).map
        (nativeRelativeDiagonalInclusion D d hd).toLinearMap := by
  ext v
  constructor
  · intro hv
    obtain ⟨h1,he⟩ := (diagonal_linear_model_mem_iff _ (nativeRelativeModelInclusion D d hd 1 v)).mp hv
    refine ⟨(nativeRelativeModelInclusion D d hd 1 v).1,h1,?_⟩
    apply Subtype.ext
    exact Prod.ext rfl he
  · rintro ⟨u,hu,rfl⟩
    change (u,u) ∈ diagonalLinearModel _
    exact diagonal_linear_model_diagonal_mem _ hu

end Hindman168
