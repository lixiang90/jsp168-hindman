import Hindman168.NativeRationalCommutatorCharacter
import Hindman168.SubgroupRealCharacterDerivedKernel
import Hindman168.NativeGroupLowerCentralExact

/-! The ACTUAL group pairing-zero condition kills the ACTUAL original Lie
commutator layer. Exact group/Lie lower-central equality is actually used;
no infinitesimal implication or smaller filtration is supplied as an oracle. -/
namespace Hindman168
open scoped Manifold ContDiff commutatorElement
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_group_commutator_le_two {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    (⊤ : Subgroup D.G).lowerCentralSeries 1 ≤ nativeRationalFilteredGroupLayer D L 2 := by
  rw [Subgroup.top_lowerCentralSeries_one,commutator_def]
  apply Subgroup.commutator_le.mpr
  intro g _ h _
  exact native_rational_original_commutator_mem_two D L g h

theorem native_rational_lie_commutator_le_two {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    nativeLieLowerCentralModel (I := D.I) (G := D.G) 1 ≤ L.layer 2 := by
  intro v hv
  have hg : nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v ∈
      (⊤ : Subgroup D.G).lowerCentralSeries 1 := by
    rw [nativeGroupLowerCentralSeries_eq_exponential (E := D.E) (I := D.I)]
    exact ⟨v,hv,rfl⟩
  have hm := (native_rational_filtered_group_logarithm_iff D L 2 _).mp
    (native_rational_group_commutator_le_two D L hg)
  rw [nativeLieGlobalLogarithm_exponential] at hm
  exact hm

theorem native_rational_difference_character_lie_commutator_zero {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker)
    (hzero : ∀ g h : D.G, nativeRationalRelativeCommutatorValue D L χ g h=0)
    (v : D.E) (hv : v ∈ nativeLieLowerCentralModel (I := D.I) (G := D.G) 1) :
    nativeRationalRelativeDifferenceCharacter D L χ
      ⟨v,native_rational_lie_commutator_le_two D L hv⟩ = 0 := by
  have hg : nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v ∈
      (⊤ : Subgroup D.G).lowerCentralSeries 1 := by
    rw [nativeGroupLowerCentralSeries_eq_exponential (E := D.E) (I := D.I)]
    exact ⟨v,hv,rfl⟩
  have hm := native_rational_group_commutator_le_two D L hg
  have he := subgroup_real_character_derived_zero _ (nativeRationalRelativeDifferenceLogCharacter D L χ)
    (native_rational_relative_difference_log_character_mul D L χ hχ)
    (native_rational_original_commutator_mem_two D L) hzero _ hm hg
  rw [native_rational_relative_difference_log_character_apply] at he
  have ht : (⟨nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
      (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v),
      (native_rational_filtered_group_logarithm_iff D L 2 _).mp hm⟩ : L.layer 2) =
      ⟨v,native_rational_lie_commutator_le_two D L hv⟩ :=
    Subtype.ext (nativeLieGlobalLogarithm_exponential (E := D.E) (I := D.I) (G := D.G) v)
  rw [ht] at he
  exact he

end Hindman168
