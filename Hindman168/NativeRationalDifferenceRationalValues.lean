import Hindman168.NativeRationalIntegralFunctionalValues
import Hindman168.NativeRationalRelativeDifferenceCharacter
import Hindman168.NativeRationalRelativeRationalFiltration

/-! Actual F_2 first-difference inclusion preserves true lattice rational
directions; actual relative lattice integrality proves rational psi values. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_first_difference_model_rational {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (v : L.layer 2) (hv : v.val ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ) :
    nativeRationalRelativeFirstDifferenceModel D L v ∈
      nativeSubgroupRationalLogSpan (E := (nativeRationalRelativeData D L 1).E)
        (I := (nativeRationalRelativeData D L 1).I) (nativeRationalRelativeData D L 1).Γ := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  apply (native_rational_relative_inclusion_rational_iff D L _).mpr
  change (v.val,0) ∈ nativeSubgroupRationalLogSpan (E := D.E × D.E)
    (I := D.I.prod D.I) (D.Γ.prod D.Γ)
  exact native_product_rational_first_mem D hv

theorem native_rational_difference_character_rational_value {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hInt : ∀ γ ∈ (nativeRationalRelativeData D L 1).Γ, ∃ z : ℤ,
      χ (nativeLieGlobalLogarithm (E := (nativeRationalRelativeData D L 1).E)
        (I := (nativeRationalRelativeData D L 1).I) (G := (nativeRationalRelativeData D L 1).G) γ) = (z : ℝ))
    (v : L.layer 2) (hv : v.val ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ) :
    ∃ q : ℚ, nativeRationalRelativeDifferenceCharacter D L χ v = (q : ℝ) :=
  native_rational_integral_functional_value (nativeRationalRelativeData D L 1) χ.toLinearMap hInt _
    (native_rational_first_difference_model_rational D L v hv)

end Hindman168
