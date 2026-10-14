import Hindman168.NativeRelativeReducedLieFiltration

/-! Both true reduced Lie initial layers are the entire ACTUAL quotient
model, from genuine Log membership and the proved group initial layers. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_relative_reduced_lie_layer_initial {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ)
    (hi : nativeRelativeReducedNativeFiltration D d hd i = ⊤) :
    nativeRelativeReducedLieFiltration D d hd i = ⊤ := by
  apply top_unique
  intro v _
  have hm : nativeLieExponential (E := (nativeRelativeReducedData D d hd).E)
      (I := (nativeRelativeReducedData D d hd).I) (G := (nativeRelativeReducedData D d hd).G) v ∈
      nativeRelativeReducedNativeFiltration D d hd i := by
    rw [hi]; exact Subgroup.mem_top _
  have he := (native_relative_reduced_layer_logarithm_iff D d hd i _).mp hm
  simpa only [nativeLieGlobalLogarithm_exponential] using he

theorem native_relative_reduced_lie_filtration_zero {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    nativeRelativeReducedLieFiltration D d hd 0 = ⊤ :=
  native_relative_reduced_lie_layer_initial D d hd 0 (native_relative_reduced_native_filtration_zero D d hd)

theorem native_relative_reduced_lie_filtration_one {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    nativeRelativeReducedLieFiltration D d hd 1 = ⊤ :=
  native_relative_reduced_lie_layer_initial D d hd 1 (native_relative_reduced_native_filtration_one D d hd)

end Hindman168
