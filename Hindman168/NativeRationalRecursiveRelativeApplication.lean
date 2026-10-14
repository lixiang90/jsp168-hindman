import Hindman168.NativeRationalRelativeRationalFiltration
import Hindman168.NativeRationalFilteredTerminal

/-! The generic relative construction is APPLIED to the ACTUAL original
terminal quotient image filtration, without replacing it by any lower
central series. These are true second-stage native groups/models/lattices. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRecursiveRelativeData {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) : NativeNilmanifoldData.{u} s :=
  nativeRationalRelativeData (nativeRelativeReducedData D d hd) (nativeReducedRationalLieFiltration D d hd) 1

noncomputable def nativeRecursiveRelativeLieFiltration {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    NativeRationalLieFiltration (nativeRecursiveRelativeData D d hd) (s*d-1) :=
  nativeRelativeRationalLieFiltration (nativeRelativeReducedData D d hd) (nativeReducedRationalLieFiltration D d hd)

theorem native_recursive_relative_group_membership {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ)
    (g : (nativeRelativeReducedData D d hd).G × (nativeRelativeReducedData D d hd).G) :
    g ∈ nativeRationalRelativeGroupLayer (nativeRelativeReducedData D d hd)
      (nativeReducedRationalLieFiltration D d hd) i ↔
    g.1 ∈ nativeRelativeReducedNativeFiltration D d hd i ∧
      g.2 ∈ nativeRelativeReducedNativeFiltration D d hd i ∧
      g.2⁻¹*g.1 ∈ nativeRelativeReducedNativeFiltration D d hd (i+1) := by
  rw [nativeRationalRelativeGroupLayer,relative_square_filtration_mem_iff]
  rw [native_reduced_rational_filtered_group_layer,native_reduced_rational_filtered_group_layer]

theorem native_recursive_relative_actual_model_layer {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    (nativeRecursiveRelativeLieFiltration D d hd).layer i =
      (relativeLinearFiltration (nativeRelativeReducedLieFiltration D d hd) i).comap
        (nativeRationalRelativeModelInclusion (nativeRelativeReducedData D d hd)
          (nativeReducedRationalLieFiltration D d hd) 1).toLinearMap := rfl

theorem native_recursive_relative_terminal_center {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    (nativeRecursiveRelativeLieFiltration D d hd).layer (s*d-1) ≤
      nativeLieCenterModel (I := (nativeRecursiveRelativeData D d hd).I)
        (G := (nativeRecursiveRelativeData D d hd).G) :=
  native_rational_filtered_terminal_central (nativeRecursiveRelativeData D d hd)
    (nativeRecursiveRelativeLieFiltration D d hd)

end Hindman168
