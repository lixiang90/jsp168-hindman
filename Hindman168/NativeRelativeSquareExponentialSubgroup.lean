import Hindman168.NativeRelativeSquareLieModel
import Hindman168.NativeRealIdealCosets

/-! The ACTUAL relative Lie algebra integrates to EXACT original
relative square, by genuine original real-ideal coset/log criteria. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_relative_square_exponential_subgroup {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d i : ℕ) :
    nativeProductLieSubgroup (nativeRelativeSquareLieAlgebra D d i) =
      nativeRelativeSquareFiltration D d i := by
  ext p
  have hm := relative_lie_subalgebra_mem_iff (L := GroupLieAlgebra D.I D.G)
    (LieModule.lowerCentralSeries ℝ (GroupLieAlgebra D.I D.G) (GroupLieAlgebra D.I D.G) ((i ⌈/⌉ d)-1))
    (LieModule.lowerCentralSeries ℝ (GroupLieAlgebra D.I D.G) (GroupLieAlgebra D.I D.G) (((i+1) ⌈/⌉ d)-1))
    (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) p.1,
      nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) p.2)
  have hn : nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) p.1 -
      nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) p.2 ∈
        nativeLieLowerCentralModel (I := D.I) (G := D.G) (((i+1) ⌈/⌉ d)-1) ↔
      p.2⁻¹*p.1 ∈ roughStretchedLowerCentralFiltration D.G d (i+1) := by
    rw [rough_native_stretched_filtration_eq (I := D.I)]
    exact native_real_ideal_coset_log_iff (I := D.I)
      (LieModule.lowerCentralSeries ℝ (GroupLieAlgebra D.I D.G) (GroupLieAlgebra D.I D.G)
        (((i+1) ⌈/⌉ d)-1)) p.1 p.2
  exact (nativeProductLieSubgroup_globalLogarithm_iff (nativeRelativeSquareLieAlgebra D d i) p).trans
    (hm.trans ((and_congr (rough_native_stretched_filtration_mem_log_iff (I := D.I) d i p.1).symm
      (and_congr (rough_native_stretched_filtration_mem_log_iff (I := D.I) d i p.2).symm hn)).trans
      (relative_square_filtration_mem_iff _ _ i p).symm))

theorem native_relative_square_native_exponential_subgroup {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d i : ℕ) :
    nativeLieSubalgebraSubgroup (E := D.E × D.E) (nativeRelativeSquareNativeLieAlgebra D d i) =
      nativeRelativeSquareFiltration D d i :=
  native_relative_square_exponential_subgroup D d i

theorem native_relative_square_filtration_simplyConnected {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d i : ℕ) :
    SimplyConnectedSpace (nativeRelativeSquareFiltration D d i) := by
  rw [← native_relative_square_exponential_subgroup D d i]
  exact nativeProductLieSubgroup_simplyConnected _

theorem native_relative_square_filtration_contractible {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d i : ℕ) :
    ContractibleSpace (nativeRelativeSquareFiltration D d i) := by
  rw [← native_relative_square_native_exponential_subgroup D d i]
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  exact nativeLieSubalgebraSubgroup_contractible _

end Hindman168
