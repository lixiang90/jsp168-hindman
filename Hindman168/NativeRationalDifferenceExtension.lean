import Hindman168.NativeRationalDifferenceRationalValues
import Hindman168.NativeRationalSplitBasisCoordinates
import Hindman168.NativeRationalFirstLayerFunctional
import Hindman168.NativeRationalDifferenceCommutatorKernel

/-! A CANONICAL genuine real extension of the actual F_2 difference
functional, zero on the fixed rational complement. Exact restriction,
rational values and actual commutator kernel are all proved. -/
namespace Hindman168
open Module
open scoped Manifold ContDiff BigOperators Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalDifferenceExtension {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) : D.E →L[ℝ] ℝ :=
  (∑ j : Fin (Module.finrank ℚ (nativeRationalFirstLayerSubspace D L)),
    nativeRationalRelativeDifferenceCharacter D L χ
      ⟨nativeRationalFirstLayerRealBasis D L (Sum.inl j),native_rational_first_layer_basis_inl_mem D L j⟩ •
        (nativeRationalFirstLayerRealBasis D L).coord (Sum.inl j)).toContinuousLinearMap

theorem native_rational_difference_extension_scalar {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) (v : D.E) :
    nativeRationalDifferenceExtension D L χ v =
      ∑ j : Fin (Module.finrank ℚ (nativeRationalFirstLayerSubspace D L)),
        nativeRationalRelativeDifferenceCharacter D L χ
          ⟨nativeRationalFirstLayerRealBasis D L (Sum.inl j),native_rational_first_layer_basis_inl_mem D L j⟩ *
            (nativeRationalFirstLayerRealBasis D L).repr v (Sum.inl j) := by
  change (∑ j, _ • (nativeRationalFirstLayerRealBasis D L).coord (Sum.inl j)) v = _
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,Basis.coord_apply]

theorem native_rational_difference_extension_restriction {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) (v : L.layer 2) :
    nativeRationalDifferenceExtension D L χ v.val = nativeRationalRelativeDifferenceCharacter D L χ v := by
  let b (j : Fin (Module.finrank ℚ (nativeRationalFirstLayerSubspace D L))) : L.layer 2 :=
    ⟨nativeRationalFirstLayerRealBasis D L (Sum.inl j),native_rational_first_layer_basis_inl_mem D L j⟩
  have hOut (i : NativeRationalFirstLayerIndex D L) :
      (nativeRationalFirstLayerRealBasis D L).repr v.val (Sum.inr i)=0 := by
    have he := native_rational_first_layer_functional_kills_two D L i v.property
    change nativeRationalFirstLayerFunctional D L i v.val = 0 at he
    rw [native_rational_first_layer_functional_coord,Basis.coord_apply] at he
    exact he
  have he := (nativeRationalFirstLayerRealBasis D L).sum_repr v.val
  rw [Fintype.sum_sum_type] at he
  have hout : (∑ i : NativeRationalFirstLayerIndex D L,
      (nativeRationalFirstLayerRealBasis D L).repr v.val (Sum.inr i) •
        nativeRationalFirstLayerRealBasis D L (Sum.inr i))=0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [hOut,zero_smul]
  rw [hout,add_zero] at he
  have hb : (∑ j, (nativeRationalFirstLayerRealBasis D L).repr v.val (Sum.inl j) • b j) = v := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum,Submodule.coe_smul,b] using he
  rw [native_rational_difference_extension_scalar]
  calc
    _ = nativeRationalRelativeDifferenceCharacter D L χ
        (∑ j, (nativeRationalFirstLayerRealBasis D L).repr v.val (Sum.inl j) • b j) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul]
      exact mul_comm _ _
    _ = _ := congrArg (nativeRationalRelativeDifferenceCharacter D L χ) hb

theorem native_rational_difference_extension_rational_value {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hInt : ∀ γ ∈ (nativeRationalRelativeData D L 1).Γ, ∃ z : ℤ,
      χ (nativeLieGlobalLogarithm (E := (nativeRationalRelativeData D L 1).E)
        (I := (nativeRationalRelativeData D L 1).I) (G := (nativeRationalRelativeData D L 1).G) γ) = (z : ℝ))
    (w : nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ) :
    ∃ q : ℚ, nativeRationalDifferenceExtension D L χ w = (q : ℝ) := by
  have hQ (j : Fin (Module.finrank ℚ (nativeRationalFirstLayerSubspace D L))) :
      ∃ q : ℚ, nativeRationalRelativeDifferenceCharacter D L χ
        ⟨nativeRationalFirstLayerRealBasis D L (Sum.inl j),native_rational_first_layer_basis_inl_mem D L j⟩ = (q : ℝ) := by
    apply native_rational_difference_character_rational_value D L χ hInt
    change nativeRationalFirstLayerRealBasis D L (Sum.inl j) ∈
      nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ
    rw [native_rational_first_layer_basis_apply]
    exact (nativeRationalFirstLayerRationalBasis D L (Sum.inl j)).property
  choose q hq using hQ
  refine ⟨∑ j, q j*(nativeRationalFirstLayerRationalBasis D L).repr w (Sum.inl j),?_⟩
  rw [native_rational_difference_extension_scalar]
  simp_rw [hq,native_rational_split_basis_coordinate_rational]
  simp only [Rat.cast_sum,Rat.cast_mul]

theorem native_rational_difference_extension_nonzero_on_two {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hne : nativeRationalRelativeDifferenceCharacter D L χ ≠ 0) :
    ∃ v : D.E, v ∈ L.layer 2 ∧ nativeRationalDifferenceExtension D L χ v ≠ 0 := by
  obtain ⟨v,hv⟩ := DFunLike.ne_iff.mp hne
  refine ⟨v.val,v.property,?_⟩
  rw [native_rational_difference_extension_restriction]
  simpa only [zero_apply] using hv

theorem native_rational_difference_extension_kills_commutator {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker)
    (hzero : ∀ g h : D.G, nativeRationalRelativeCommutatorValue D L χ g h=0) :
    nativeLieLowerCentralModel (I := D.I) (G := D.G) 1 ≤ (nativeRationalDifferenceExtension D L χ).toLinearMap.ker := by
  intro v hv
  have he := native_rational_difference_extension_restriction D L χ
    ⟨v,native_rational_lie_commutator_le_two D L hv⟩
  change nativeRationalDifferenceExtension D L χ v = 0
  exact he.trans (native_rational_difference_character_lie_commutator_zero D L χ hχ hzero v hv)

end Hindman168
