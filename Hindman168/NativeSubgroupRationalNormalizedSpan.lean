import Hindman168.NativeLieRationalInternalBCH

/-! Actual subgroup conjugation invariance implies invariance of the
actual Q log span under brackets with the normalizing subgroup's log
span. Integer adjoint curves supply the coefficients. No normality of
the original lattice in the ambient group is asserted. -/

namespace Hindman168
open Function Set Submodule
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeSubgroupRationalLogSpan_mono {Δ K : Subgroup G} (h : Δ ≤ K) :
    nativeSubgroupRationalLogSpan (E := E) (I := I) Δ ≤
      nativeSubgroupRationalLogSpan (E := E) (I := I) K := by
  exact Submodule.span_mono (Set.image_mono h)

 theorem nativeSubgroupRationalLogSpan_adjoint_mem_of_conjugation
    (Δ : Subgroup G) (g : G) (hconj : ∀ h ∈ Δ, g * h * g⁻¹ ∈ Δ)
    {w : E} (hw : w ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Δ) :
    (nativeLieAdjoint (I := I) g : E →L[ℝ] E) w ∈
      nativeSubgroupRationalLogSpan (E := E) (I := I) Δ := by
  let S : Submodule ℚ E := nativeSubgroupRationalLogSpan (E := E) (I := I) Δ
  let A : E →ₗ[ℚ] E := (nativeLieAdjoint (I := I) g).toLinearMap.restrictScalars ℚ
  have hle : S ≤ S.comap A := by
    apply Submodule.span_le.mpr
    rintro v ⟨h, hh, rfl⟩
    change (nativeLieAdjoint (I := I) g : E →L[ℝ] E)
      (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) h) ∈ S
    rw [nativeLieAdjoint_logarithm_conjugation]
    exact nativeSubgroup_logarithm_mem_span Δ (hconj h hh)
  exact hle hw

 theorem nativeLieAdjointGenerator_logarithms_mem_normalized_span
    (K Δ : Subgroup G) (hconj : ∀ g ∈ K, ∀ h ∈ Δ, g * h * g⁻¹ ∈ Δ)
    {g h : G} (hg : g ∈ K) (hh : h ∈ Δ) :
    nativeLieAdjointGenerator (I := I) (G := G)
      (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g)
      (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) h) ∈
        nativeSubgroupRationalLogSpan (E := E) (I := I) Δ := by
  let v : E := nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g
  let w : E := nativeLieGlobalLogarithm (E := E) (I := I) (G := G) h
  have he : nativeLieExponential (I := I) (G := G) v = g :=
    nativeLieExponential_globalLogarithm (E := E) (I := I) (G := G) g
  apply nativeLieAdjointGenerator_mem_of_nat_curve_values
  intro n
  have ht : lieOneParameterCurve (I := I) (G := G) v (n : ℝ) = g ^ n := by
    calc
      _ = (lieOneParameterCurve (I := I) (G := G) v 1) ^ n := by
        simpa only [mul_one] using lieOneParameterCurve_nat_mul (E := E) (I := I) (G := G) v n 1
      _ = g ^ n := congrArg (fun a : G => a ^ n) he
  change (nativeLieAdjoint (I := I) (lieOneParameterCurve (I := I) (G := G) v (n : ℝ)) : E →L[ℝ] E) w ∈ _
  rw [ht]
  exact nativeSubgroupRationalLogSpan_adjoint_mem_of_conjugation Δ (g ^ n)
    (hconj (g ^ n) (K.pow_mem hg n)) (nativeSubgroup_logarithm_mem_span Δ hh)

 theorem nativeSubgroupRationalLogSpan_differential_mem_of_normalized
    (K Δ : Subgroup G) (hconj : ∀ g ∈ K, ∀ h ∈ Δ, g * h * g⁻¹ ∈ Δ)
    {v w : E} (hv : v ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) K)
    (hw : w ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Δ) :
    nativeLieAdjointDifferential (I := I) (G := G) v w ∈
      nativeSubgroupRationalLogSpan (E := E) (I := I) Δ := by
  let S : Submodule ℚ E := nativeSubgroupRationalLogSpan (E := E) (I := I) Δ
  let T : Submodule ℚ E := nativeSubgroupRationalLogSpan (E := E) (I := I) K
  let B : E →L[ℝ] (E →L[ℝ] E) := nativeLieAdjointDifferential (I := I) (G := G)
  have hGenerators : ∀ g ∈ K, ∀ h ∈ Δ,
      B (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g)
        (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) h) ∈ S := by
    intro g hg h hh
    have hgen := nativeLieAdjointGenerator_logarithms_mem_normalized_span (E := E) (I := I) (G := G) K Δ hconj hg hh
    rw [nativeLieAdjointGenerator_eq_differential] at hgen
    exact hgen
  have hsecond : ∀ g ∈ K, ∀ y ∈ S,
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
  have hle : T ≤ S.comap A := by
    apply Submodule.span_le.mpr
    rintro z ⟨g, hg, rfl⟩
    exact hsecond g hg w hw
  exact hle hv

 theorem nativeSubgroupRationalLogSpan_bracket_mem_of_normalized
    (K Δ : Subgroup G) (hconj : ∀ g ∈ K, ∀ h ∈ Δ, g * h * g⁻¹ ∈ Δ)
    (v w : GroupLieAlgebra I G)
    (hv : v ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) K)
    (hw : w ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Δ) :
    ⁅v, w⁆ ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Δ := by
  have hb := nativeSubgroupRationalLogSpan_differential_mem_of_normalized (E := E) (I := I) (G := G) K Δ hconj hv hw
  have he : nativeLieAdjointDifferential (E := E) (I := I) (G := G) v w =
      (⁅v, w⁆ : GroupLieAlgebra I G) := by
    rw [← nativeLieAdjointGenerator_eq_differential (E := E) (I := I) (G := G)]
    exact nativeLieAdjointGenerator_eq_native_bracket (I := I) (G := G) v w
  exact he ▸ hb

end Hindman168
