import Hindman168.NativeRationalTerminalExponentialLogarithm
import Hindman168.NativeLatticeRationalCoordinates

/-! Actual original native terminal quotient projection, identity differential and Exp/Log/rational span transport. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_terminal_rational_mem {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    {v : D.E}
    (hv : v ∈ nativeSubgroupRationalLogSpan (E := D.E)
      (I := D.I) D.Γ) :
    nativeRationalTerminalModelProjection D F v ∈ nativeSubgroupRationalLogSpan
      (E := (nativeRationalTerminalQuotientData D F).E) (I := (nativeRationalTerminalQuotientData D F).I)
        (nativeRationalTerminalQuotientData D F).Γ := by
  obtain ⟨n,hn,hp⟩ := (nativeSubgroupRationalLogSpan_mem_iff_positive_power
    (I := D.I) D.Γ v).mp hv
  apply (nativeSubgroupRationalLogSpan_mem_iff_positive_power
    (I := (nativeRationalTerminalQuotientData D F).I) (nativeRationalTerminalQuotientData D F).Γ _).mpr
  refine ⟨n,hn,?_⟩
  have he := (map_pow (nativeRationalTerminalGroupProjection D F)
    (nativeLieExponential (E := D.E)
      (I := D.I)
      (G := D.G) v) n).trans
        (congrArg (fun g => g^n) (native_rational_terminal_data_exponential D F v))
  exact he ▸ (Subgroup.mem_map_of_mem (nativeRationalTerminalGroupProjection D F) hp)

theorem native_rational_terminal_logarithm_image {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    (nativeRationalTerminalModelProjection D F) ''
      ((nativeLieGlobalLogarithm (E := D.E)
        (I := D.I) (G := D.G)) ''
          (D.Γ : Set D.G)) =
      (nativeLieGlobalLogarithm (E := (nativeRationalTerminalQuotientData D F).E)
        (I := (nativeRationalTerminalQuotientData D F).I) (G := (nativeRationalTerminalQuotientData D F).G)) ''
          ((nativeRationalTerminalQuotientData D F).Γ : Set (nativeRationalTerminalQuotientData D F).G) := by
  letI := native_rational_terminal_subgroup_normal D F
  have he : (nativeRationalTerminalModelProjection D F) ∘
      (nativeLieGlobalLogarithm (E := D.E)
        (I := D.I) (G := D.G)) =
      (nativeLieGlobalLogarithm (E := (nativeRationalTerminalQuotientData D F).E)
        (I := (nativeRationalTerminalQuotientData D F).I) (G := (nativeRationalTerminalQuotientData D F).G)) ∘
          (nativeRationalTerminalGroupProjection D F) :=
    funext (fun g => (native_rational_terminal_data_logarithm D F g).symm)
  change _ = (nativeLieGlobalLogarithm (E := (nativeRationalTerminalQuotientData D F).E)
    (I := (nativeRationalTerminalQuotientData D F).I) (G := (nativeRationalTerminalQuotientData D F).G)) ''
      (D.Γ.map (nativeRationalTerminalGroupProjection D F) :
        Set (nativeRationalTerminalQuotientData D F).G)
  rw [Subgroup.coe_map,← Set.image_comp,← Set.image_comp,he]

theorem native_rational_terminal_rational_span_map {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    (nativeSubgroupRationalLogSpan (E := D.E)
      (I := D.I) D.Γ).map
        ((nativeRationalTerminalModelProjection D F).toLinearMap.restrictScalars ℚ) =
      nativeSubgroupRationalLogSpan (E := (nativeRationalTerminalQuotientData D F).E)
        (I := (nativeRationalTerminalQuotientData D F).I) (nativeRationalTerminalQuotientData D F).Γ := by
  exact (Submodule.map_span ((nativeRationalTerminalModelProjection D F).toLinearMap.restrictScalars ℚ)
    ((nativeLieGlobalLogarithm (E := D.E)
      (I := D.I) (G := D.G)) ''
        (D.Γ : Set D.G))).trans
      (congrArg (Submodule.span ℚ) (native_rational_terminal_logarithm_image D F))

end Hindman168
