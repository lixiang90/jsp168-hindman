import Hindman168.NativeRelativeInclusion
import Hindman168.NativeProductAdjointDifferential
import Hindman168.RelativeLinearFiltration
import Hindman168.RoughNativeStretchedLieBracket

/-! SAME actual relative native Lie-model filtration. Its genuine bracket
condition is transported through ACTUAL smooth inclusion/identity derivative,
not assumed as an abstract compatibility input. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_relative_ambient_lie_layer_eq {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d i : ℕ) :
    relativeLinearFiltration (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) d) i =
      nativeRelativeSquareModel D d i := by
  ext v
  change v ∈ relativeLinearModel
    (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) d i)
    (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) d (i+1)) ↔ _
  rw [relative_linear_model_mem_iff,native_relative_square_model_mem_iff]
  rfl

noncomputable def nativeRelativeLieFiltration {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    Submodule ℝ (nativeRelativeSquareData D d hd 1).E :=
  (nativeRelativeSquareModel D d i).comap (nativeRelativeModelInclusion D d hd 1).toLinearMap

theorem native_relative_lie_filtration_antitone {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    Antitone (nativeRelativeLieFiltration D d hd) := by
  intro i j hij
  have he := relative_linear_filtration_antitone _ (rough_native_stretched_lie_antitone (I := D.I) (G := D.G) d hd) hij
  rw [native_relative_ambient_lie_layer_eq D d j,native_relative_ambient_lie_layer_eq D d i] at he
  exact Submodule.comap_mono he

theorem native_relative_lie_filtration_zero {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    nativeRelativeLieFiltration D d hd 0 = ⊤ := by
  have he := relative_linear_filtration_zero
    (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) d)
    (rough_native_stretched_lie_initial d hd 0 (Nat.zero_le d))
    (rough_native_stretched_lie_initial d hd 1 hd)
  rw [native_relative_ambient_lie_layer_eq D d 0] at he
  simp only [nativeRelativeLieFiltration,he,Submodule.comap_top]

theorem native_relative_lie_filtration_one {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    nativeRelativeLieFiltration D d hd 1 = ⊤ := by
  apply top_unique
  intro v _
  change (nativeRelativeModelInclusion D d hd 1 v) ∈ nativeRelativeSquareModel D d 1
  rw [← native_relative_square_native_model_eq D d 1]
  exact v.property

theorem native_relative_model_adjoint_differential {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (v w : (nativeRelativeSquareData D d hd 1).E) :
    nativeRelativeModelInclusion D d hd 1
      (nativeLieAdjointDifferential (I := (nativeRelativeSquareData D d hd 1).I)
        (G := (nativeRelativeSquareData D d hd 1).G) v w) =
    nativeLieAdjointDifferential (I := D.I.prod D.I) (G := D.G × D.G)
      (nativeRelativeModelInclusion D d hd 1 v) (nativeRelativeModelInclusion D d hd 1 w) := by
  have he := nativeSmoothHom_generator_intertwine
    (E := (nativeRelativeSquareData D d hd 1).E) (F := D.E × D.E)
    (I := (nativeRelativeSquareData D d hd 1).I) (J := D.I.prod D.I)
    (nativeRelativeGroupInclusion D d hd 1) (native_relative_inclusion_contMDiff D d hd 1) v w
  rw [native_relative_inclusion_mfderiv] at he
  simpa only [nativeLieAdjointGenerator_eq_differential] using he

theorem native_relative_lie_filtration_bracket {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    {i j : ℕ} {v w : (nativeRelativeSquareData D d hd 1).E}
    (hv : v ∈ nativeRelativeLieFiltration D d hd i) (hw : w ∈ nativeRelativeLieFiltration D d hd j) :
    nativeLieAdjointDifferential (I := (nativeRelativeSquareData D d hd 1).I)
      (G := (nativeRelativeSquareData D d hd 1).G) v w ∈ nativeRelativeLieFiltration D d hd (i+j) := by
  change nativeRelativeModelInclusion D d hd 1
    (nativeLieAdjointDifferential (I := (nativeRelativeSquareData D d hd 1).I)
      (G := (nativeRelativeSquareData D d hd 1).G) v w) ∈ nativeRelativeSquareModel D d (i+j)
  rw [native_relative_model_adjoint_differential,
    native_product_adjoint_differential (I := D.I) (J := D.I) (G := D.G) (K := D.G),
    ← native_relative_ambient_lie_layer_eq D d (i+j)]
  apply relative_linear_filtration_bilinear _ (nativeLieAdjointDifferential (I := D.I) (G := D.G))
    (fun _ _ _ _ h1 h2 => rough_native_stretched_lie_bracket d hd h1 h2)
  · rw [native_relative_ambient_lie_layer_eq D d i]; exact hv
  · rw [native_relative_ambient_lie_layer_eq D d j]; exact hw

end Hindman168
