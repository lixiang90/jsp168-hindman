import Hindman168.NativeRelativeReductionExponentialLogarithm
import Hindman168.NativeLatticeRationalCoordinates

/-! The actual terminal quotient projection sends the original restricted
lattice rational span to the actual image lattice rational span. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_relative_reduction_rational_mem {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    {v : (nativeRelativeSquareData D d hd 1).E}
    (hv : v ∈ nativeSubgroupRationalLogSpan (E := (nativeRelativeSquareData D d hd 1).E)
      (I := (nativeRelativeSquareData D d hd 1).I) (nativeRelativeSquareData D d hd 1).Γ) :
    nativeRelativeReductionModelProjection D d hd v ∈ nativeSubgroupRationalLogSpan
      (E := (nativeRelativeReducedData D d hd).E) (I := (nativeRelativeReducedData D d hd).I)
        (nativeRelativeReducedData D d hd).Γ := by
  obtain ⟨n,hn,hp⟩ := (nativeSubgroupRationalLogSpan_mem_iff_positive_power
    (I := (nativeRelativeSquareData D d hd 1).I) (nativeRelativeSquareData D d hd 1).Γ v).mp hv
  apply (nativeSubgroupRationalLogSpan_mem_iff_positive_power
    (I := (nativeRelativeReducedData D d hd).I) (nativeRelativeReducedData D d hd).Γ _).mpr
  refine ⟨n,hn,?_⟩
  have he := (map_pow (nativeRelativeReductionGroupProjection D d hd)
    (nativeLieExponential (E := (nativeRelativeSquareData D d hd 1).E)
      (I := (nativeRelativeSquareData D d hd 1).I)
      (G := (nativeRelativeSquareData D d hd 1).G) v) n).trans
        (congrArg (fun g => g^n) (native_relative_reduction_data_exponential D d hd v))
  exact he ▸ (Subgroup.mem_map_of_mem (nativeRelativeReductionGroupProjection D d hd) hp)

theorem native_relative_reduction_logarithm_image {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    (nativeRelativeReductionModelProjection D d hd) ''
      ((nativeLieGlobalLogarithm (E := (nativeRelativeSquareData D d hd 1).E)
        (I := (nativeRelativeSquareData D d hd 1).I) (G := (nativeRelativeSquareData D d hd 1).G)) ''
          ((nativeRelativeSquareData D d hd 1).Γ : Set (nativeRelativeSquareData D d hd 1).G)) =
      (nativeLieGlobalLogarithm (E := (nativeRelativeReducedData D d hd).E)
        (I := (nativeRelativeReducedData D d hd).I) (G := (nativeRelativeReducedData D d hd).G)) ''
          ((nativeRelativeReducedData D d hd).Γ : Set (nativeRelativeReducedData D d hd).G) := by
  letI := native_relative_terminal_subgroup_normal D d hd
  have he : (nativeRelativeReductionModelProjection D d hd) ∘
      (nativeLieGlobalLogarithm (E := (nativeRelativeSquareData D d hd 1).E)
        (I := (nativeRelativeSquareData D d hd 1).I) (G := (nativeRelativeSquareData D d hd 1).G)) =
      (nativeLieGlobalLogarithm (E := (nativeRelativeReducedData D d hd).E)
        (I := (nativeRelativeReducedData D d hd).I) (G := (nativeRelativeReducedData D d hd).G)) ∘
          (nativeRelativeReductionGroupProjection D d hd) :=
    funext (fun g => (native_relative_reduction_data_logarithm D d hd g).symm)
  change _ = (nativeLieGlobalLogarithm (E := (nativeRelativeReducedData D d hd).E)
    (I := (nativeRelativeReducedData D d hd).I) (G := (nativeRelativeReducedData D d hd).G)) ''
      ((nativeRelativeSquareData D d hd 1).Γ.map (nativeRelativeReductionGroupProjection D d hd) :
        Set (nativeRelativeReducedData D d hd).G)
  rw [Subgroup.coe_map,← Set.image_comp,← Set.image_comp,he]

theorem native_relative_reduction_rational_span_map {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    (nativeSubgroupRationalLogSpan (E := (nativeRelativeSquareData D d hd 1).E)
      (I := (nativeRelativeSquareData D d hd 1).I) (nativeRelativeSquareData D d hd 1).Γ).map
        ((nativeRelativeReductionModelProjection D d hd).toLinearMap.restrictScalars ℚ) =
      nativeSubgroupRationalLogSpan (E := (nativeRelativeReducedData D d hd).E)
        (I := (nativeRelativeReducedData D d hd).I) (nativeRelativeReducedData D d hd).Γ := by
  exact (Submodule.map_span ((nativeRelativeReductionModelProjection D d hd).toLinearMap.restrictScalars ℚ)
    ((nativeLieGlobalLogarithm (E := (nativeRelativeSquareData D d hd 1).E)
      (I := (nativeRelativeSquareData D d hd 1).I) (G := (nativeRelativeSquareData D d hd 1).G)) ''
        ((nativeRelativeSquareData D d hd 1).Γ : Set (nativeRelativeSquareData D d hd 1).G))).trans
      (congrArg (Submodule.span ℚ) (native_relative_reduction_logarithm_image D d hd))

end Hindman168
