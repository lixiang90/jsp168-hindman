import Hindman168.RoughConjugateLatticeTopology
import Hindman168.NativeSubgroupBracketSpan

namespace Hindman168
open Set Submodule
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_adjoint_mem_conjugate_span (Γ : Subgroup G) (g : G)
    {w : E} (hw : w ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ) :
    (nativeLieAdjoint (I := I) g : E →L[ℝ] E) w ∈
      nativeSubgroupRationalLogSpan (E := E) (I := I) (roughConjugateSubgroup Γ g) := by
  let W := nativeSubgroupRationalLogSpan (E := E) (I := I) Γ
  let T := nativeSubgroupRationalLogSpan (E := E) (I := I) (roughConjugateSubgroup Γ g)
  let A : E →ₗ[ℚ] E := (nativeLieAdjoint (I := I) g).toLinearMap.restrictScalars ℚ
  have hle : W ≤ T.comap A := by
    apply Submodule.span_le.mpr
    rintro x ⟨h, hh, rfl⟩
    change (nativeLieAdjoint (I := I) g : E →L[ℝ] E)
      (nativeLieGlobalLogarithm (E := E) (I := I) h) ∈ T
    rw [nativeLieAdjoint_logarithm_conjugation]
    exact nativeSubgroup_logarithm_mem_span _ ((roughConjugateSubgroup_mem Γ g h).mpr hh)
  exact hle hw

theorem rough_native_conjugate_log_span (Γ : Subgroup G) {v : E}
    (hv : v ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ) :
    nativeSubgroupRationalLogSpan (E := E) (I := I)
      (roughConjugateSubgroup Γ (nativeLieExponential (I := I) (G := G) v)) =
        nativeSubgroupRationalLogSpan (E := E) (I := I) Γ := by
  let W := nativeSubgroupRationalLogSpan (E := E) (I := I) Γ
  let g : G := nativeLieExponential (I := I) (G := G) v
  have hbr := nativeSubgroupRationalLogSpan_bracket_closed (I := I) Γ
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨h, hh, rfl⟩
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hh
    change nativeLieGlobalLogarithm (E := E) (I := I) (g*k*g⁻¹) ∈ W
    rw [← nativeLieAdjoint_logarithm_conjugation]
    exact nativeLieAdjoint_exponential_mem_rational W hbr hv (nativeSubgroup_logarithm_mem_span Γ hk)
  · intro w hw
    have hneg : (nativeLieAdjoint (I := I)
        (nativeLieExponential (I := I) (G := G) (-v)) : E →L[ℝ] E) w ∈ W :=
      nativeLieAdjoint_exponential_mem_rational W hbr (W.neg_mem hv) hw
    have he : nativeLieExponential (I := I) (G := G) (-v) = g⁻¹ :=
      nativeLieExponential_neg (I := I) (G := G) v
    rw [he] at hneg
    have ht := rough_native_adjoint_mem_conjugate_span (I := I) Γ g hneg
    rw [nativeLieAdjoint_apply_inv] at ht
    exact ht

end Hindman168
