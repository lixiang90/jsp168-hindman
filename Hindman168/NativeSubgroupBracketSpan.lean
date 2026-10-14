import Hindman168.NativeSubgroupLogarithmSpan

/-! The original rational span of logarithms of any specified subgroup
is closed under the original native Lie bracket. Integer conjugations
supply actual adjoint polynomial values; algebraic coefficient extraction
recovers the actual generator. Bilinearity extends from original logarithm
generators to their actual Q-linear span. No bracket closure is assumed. -/

namespace Hindman168
open Function Set Submodule
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieAdjointGenerator_logarithms_mem_span (Γ : Subgroup G)
    {g h : G} (hg : g ∈ Γ) (hh : h ∈ Γ) :
    nativeLieAdjointGenerator (I := I) (G := G)
      (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g)
      (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) h) ∈
        nativeSubgroupRationalLogSpan (E := E) (I := I) Γ := by
  let v : E := nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g
  let w : E := nativeLieGlobalLogarithm (E := E) (I := I) (G := G) h
  let exp : E → G := fun v => nativeLieExponential (I := I) (G := G) v
  have he : exp v = g := nativeLieExponential_globalLogarithm (E := E) (I := I) (G := G) g
  apply nativeLieAdjointGenerator_mem_of_nat_curve_values
  intro n
  have ht : lieOneParameterCurve (I := I) (G := G) v (n : ℝ) = g ^ n := by
    calc
      _ = (lieOneParameterCurve (I := I) (G := G) v 1) ^ n := by
        simpa only [mul_one] using lieOneParameterCurve_nat_mul (E := E) (I := I) (G := G) v n 1
      _ = g ^ n := congrArg (fun a : G => a ^ n) he
  change (nativeLieAdjoint (I := I) (lieOneParameterCurve (I := I) (G := G) v (n : ℝ)) : E →L[ℝ] E) w ∈ _
  rw [ht]
  exact nativeSubgroupRationalLogSpan_adjoint_mem (E := E) (I := I) Γ (Γ.pow_mem hg n)
    (nativeSubgroup_logarithm_mem_span (E := E) (I := I) Γ hh)

 theorem nativeSubgroupRationalLogSpan_differential_mem (Γ : Subgroup G)
    {v w : E} (hv : v ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ)
    (hw : w ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ) :
    nativeLieAdjointDifferential (I := I) (G := G) v w ∈
      nativeSubgroupRationalLogSpan (E := E) (I := I) Γ := by
  let S : Submodule ℚ E := nativeSubgroupRationalLogSpan (E := E) (I := I) Γ
  let B : E →L[ℝ] (E →L[ℝ] E) := nativeLieAdjointDifferential (I := I) (G := G)
  have hGenerators : ∀ g ∈ Γ, ∀ h ∈ Γ,
      B (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g)
        (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) h) ∈ S := by
    intro g hg h hh
    have hgen := nativeLieAdjointGenerator_logarithms_mem_span (E := E) (I := I) Γ hg hh
    rw [nativeLieAdjointGenerator_eq_differential] at hgen
    exact hgen
  have hsecond : ∀ g ∈ Γ, ∀ y ∈ S,
      B (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g) y ∈ S := by
    intro g hg y hy
    let A : E →ₗ[ℚ] E :=
      (B (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g)).toLinearMap.restrictScalars ℚ
    have hle : S ≤ S.comap A := by
      apply Submodule.span_le.mpr
      rintro z ⟨h, hh, rfl⟩
      exact hGenerators g hg h hh
    exact hle hy
  let A : E →ₗ[ℚ] E := (B.flip w).toLinearMap.restrictScalars ℚ
  have hle : S ≤ S.comap A := by
    apply Submodule.span_le.mpr
    rintro z ⟨g, hg, rfl⟩
    exact hsecond g hg w hw
  exact hle hv

 theorem nativeSubgroupRationalLogSpan_bracket_closed (Γ : Subgroup G) :
    nativeLieRationalBracketClosed (E := E) (I := I) (G := G)
      (nativeSubgroupRationalLogSpan (E := E) (I := I) Γ) := by
  intro x y hx hy
  have hd : nativeLieAdjointDifferential (I := I) (G := G) x y ∈
      nativeSubgroupRationalLogSpan (E := E) (I := I) Γ :=
    nativeSubgroupRationalLogSpan_differential_mem (E := E) (I := I) Γ hx hy
  have he : nativeLieAdjointDifferential (I := I) (G := G) x y = (⁅x, y⁆ : GroupLieAlgebra I G) := by
    rw [← nativeLieAdjointGenerator_eq_differential]
    exact nativeLieAdjointGenerator_eq_native_bracket (I := I) (G := G) x y
  exact he ▸ hd

 theorem nativeSubgroupRationalLogSpan_product_logarithm_mem (Γ : Subgroup G)
    {u w : E} (hu : u ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ)
    (hw : w ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ) :
    nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
      (nativeLieExponential (I := I) (G := G) u * nativeLieExponential (I := I) (G := G) w) ∈
        nativeSubgroupRationalLogSpan (E := E) (I := I) Γ :=
  nativeLieRationalBCH_mem _ (nativeSubgroupRationalLogSpan_bracket_closed (E := E) (I := I) Γ) hu hw

end Hindman168
