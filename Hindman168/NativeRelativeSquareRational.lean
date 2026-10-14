import Hindman168.NativeRelativeSquareLieModel
import Hindman168.RelativeLinearModelSpan
import Hindman168.NativeProductRationalInclusions
import Hindman168.NativeLieLayerLatticeCompact

/-! GENUINE original product-lattice rationality of every ACTUAL
stretched relative-square model. Original rational layers and genuine
diagonal/coordinate rational inclusions span the ENTIRE actual model. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_relative_square_model_rational {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
    nativeLatticeRationalSubspace (E := D.E × D.E) (I := D.I.prod D.I)
      (D.Γ.prod D.Γ) (nativeRelativeSquareModel D d i) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  let A := nativeLieLowerCentralModel (I := D.I) (G := D.G) ((i ⌈/⌉ d)-1)
  let B := nativeLieLowerCentralModel (I := D.I) (G := D.G) (((i+1) ⌈/⌉ d)-1)
  let W := nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ
  have hBA : B ≤ A := nativeLieLowerCentralModel_antitone (I := D.I)
    (Nat.sub_le_sub_right (rough_ceiling_index_monotone d hd (Nat.le_succ i)) 1)
  have hA : Submodule.span ℝ ((A.restrictScalars ℚ ⊓ W : Submodule ℚ D.E) : Set D.E) = A :=
    nativeLieLowerCentralModel_lattice_rational (I := D.I) D.Γ ((i ⌈/⌉ d)-1)
  have hB : Submodule.span ℝ ((B.restrictScalars ℚ ⊓ W : Submodule ℚ D.E) : Set D.E) = B :=
    nativeLieLowerCentralModel_lattice_rational (I := D.I) D.Γ (((i+1) ⌈/⌉ d)-1)
  have hmodel : nativeRelativeSquareModel D d i =
      A.map ((LinearMap.id : D.E →ₗ[ℝ] D.E).prod LinearMap.id) ⊔
        B.map (LinearMap.inl ℝ D.E D.E) := relative_linear_model_eq_span_maps A B hBA
  unfold nativeLatticeRationalSubspace
  apply le_antisymm
  · exact Submodule.span_le.mpr (fun _ hv => hv.1)
  · conv_lhs => rw [hmodel]
    apply sup_le
    · rw [← hA,Submodule.map_span]
      apply Submodule.span_le.mpr
      rintro v ⟨w,hw,rfl⟩
      apply Submodule.subset_span
      refine ⟨?_,native_product_rational_diagonal_mem D hw.2⟩
      exact relative_linear_model_diagonal_mem A B hw.1
    · rw [← hB,Submodule.map_span]
      apply Submodule.span_le.mpr
      rintro v ⟨w,hw,rfl⟩
      apply Submodule.subset_span
      refine ⟨?_,native_product_rational_first_mem D hw.2⟩
      exact relative_linear_model_first_mem A B hBA hw.1

theorem native_relative_square_native_model_rational {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
    nativeLatticeRationalSubspace (E := D.E × D.E) (I := D.I.prod D.I) (D.Γ.prod D.Γ)
      (nativeLieSubalgebraModel (nativeRelativeSquareNativeLieAlgebra D d i)) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  rw [native_relative_square_native_model_eq]
  exact native_relative_square_model_rational D d hd i

end Hindman168
