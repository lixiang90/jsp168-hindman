import Hindman168.NativeRationalFilteredGroupBrackets
import Hindman168.NativeProductLieModel
import Hindman168.RelativeLinearFiltration
import Hindman168.RelativeSquareFiltration

/-! Genuine relative square for ANY actual rational native Lie filtration,
including the original terminal quotient image filtration. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalRelativeLieSubalgebra {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    LieSubalgebra ℝ (GroupLieAlgebra D.I D.G × GroupLieAlgebra D.I D.G) :=
  relativeLieSubalgebra (nativeRationalFilteredLieIdeal D F i) (nativeRationalFilteredLieIdeal D F (i+1))

noncomputable def nativeRationalRelativeNativeSubalgebra {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    LieSubalgebra ℝ (GroupLieAlgebra (D.I.prod D.I) (D.G × D.G)) :=
  (nativeRationalRelativeLieSubalgebra D F i).map
    (nativeProductLieEquiv (I := D.I) (J := D.I) (G := D.G) (K := D.G)).symm.toLieHom

noncomputable def nativeRationalRelativeGroupLayer {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) : Subgroup (D.G × D.G) :=
  relativeSquareFiltration (nativeRationalFilteredGroupLayer D F) (native_rational_filtered_group_normal D F) i

theorem native_rational_relative_subalgebra_model {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    nativeLieSubalgebraModel (nativeRationalRelativeNativeSubalgebra D F i) =
      relativeLinearFiltration F.layer i :=
  nativeProductLieModel_map_eq (nativeRationalRelativeLieSubalgebra D F i)

theorem native_rational_relative_product_subgroup_eq {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    nativeProductLieSubgroup (nativeRationalRelativeLieSubalgebra D F i) = nativeRationalRelativeGroupLayer D F i := by
  ext p
  have hm := relative_lie_subalgebra_mem_iff (nativeRationalFilteredLieIdeal D F i)
    (nativeRationalFilteredLieIdeal D F (i+1))
    (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) p.1,
      nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) p.2)
  have hn := native_rational_filtered_group_coset_log_iff D F (i+1) p.1 p.2
  exact (nativeProductLieSubgroup_globalLogarithm_iff (nativeRationalRelativeLieSubalgebra D F i) p).trans
    (hm.trans ((and_congr (native_rational_filtered_group_logarithm_iff D F i p.1).symm
      (and_congr (native_rational_filtered_group_logarithm_iff D F i p.2).symm hn)).trans
        (relative_square_filtration_mem_iff _ _ i p).symm))

theorem native_rational_relative_native_subgroup_eq {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    nativeLieSubalgebraSubgroup (E := D.E × D.E) (nativeRationalRelativeNativeSubalgebra D F i) =
      nativeRationalRelativeGroupLayer D F i := native_rational_relative_product_subgroup_eq D F i

theorem native_rational_relative_group_conditions {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    CubeGroupFiltration (nativeRationalRelativeGroupLayer D F) :=
  relative_square_filtration_conditions _ (native_rational_filtered_group_normal D F)
    (native_rational_filtered_group_conditions D F)

end Hindman168
