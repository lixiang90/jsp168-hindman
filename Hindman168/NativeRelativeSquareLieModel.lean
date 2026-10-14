import Hindman168.NativeRelativeSquareFiltration
import Hindman168.RelativeLieSubalgebra
import Hindman168.NativeProductLieModel

/-! Actual original relative-square Lie algebra and its actual product
tangent model, using the same original stretched lower-central layers. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRelativeSquareLieAlgebra {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (d i : ℕ) : LieSubalgebra ℝ (GroupLieAlgebra D.I D.G × GroupLieAlgebra D.I D.G) :=
  relativeLieSubalgebra
    (LieModule.lowerCentralSeries ℝ (GroupLieAlgebra D.I D.G) (GroupLieAlgebra D.I D.G) ((i ⌈/⌉ d)-1))
    (LieModule.lowerCentralSeries ℝ (GroupLieAlgebra D.I D.G) (GroupLieAlgebra D.I D.G) (((i+1) ⌈/⌉ d)-1))

noncomputable def nativeRelativeSquareModel {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (d i : ℕ) : Submodule ℝ (D.E × D.E) :=
  nativeProductLieModel (nativeRelativeSquareLieAlgebra D d i)

noncomputable def nativeRelativeSquareNativeLieAlgebra {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d i : ℕ) :
    LieSubalgebra ℝ (GroupLieAlgebra (D.I.prod D.I) (D.G × D.G)) :=
  (nativeRelativeSquareLieAlgebra D d i).map
    (nativeProductLieEquiv (I := D.I) (J := D.I) (G := D.G) (K := D.G)).symm.toLieHom

theorem native_relative_square_model_mem_iff {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d i : ℕ) (v : D.E × D.E) :
    v ∈ nativeRelativeSquareModel D d i ↔
      v.1 ∈ nativeLieLowerCentralModel (I := D.I) (G := D.G) ((i ⌈/⌉ d)-1) ∧
      v.2 ∈ nativeLieLowerCentralModel (I := D.I) (G := D.G) ((i ⌈/⌉ d)-1) ∧
      v.1-v.2 ∈ nativeLieLowerCentralModel (I := D.I) (G := D.G) (((i+1) ⌈/⌉ d)-1) :=
  relative_lie_subalgebra_mem_iff (L := GroupLieAlgebra D.I D.G) _ _ v

theorem native_relative_square_native_model_eq {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d i : ℕ) :
    nativeLieSubalgebraModel (E := D.E × D.E) (nativeRelativeSquareNativeLieAlgebra D d i) =
      nativeRelativeSquareModel D d i :=
  nativeProductLieModel_map_eq _

end Hindman168
