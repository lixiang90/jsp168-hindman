import Hindman168.NativeLieAdjointNatPolynomial

/-! The original global logarithms of an arbitrary specified subgroup
generate an actual Q-linear space. Original subgroup conjugation and the
genuine exponential/logarithm inverse laws prove adjoint invariance of
this space. No additive subgroup law for the original logarithm set is used. -/

namespace Hindman168
open Function Set Submodule
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeSubgroupRationalLogSpan (Γ : Subgroup G) : Submodule ℚ E :=
  span ℚ ((nativeLieGlobalLogarithm (E := E) (I := I) (G := G)) '' (Γ : Set G))

 theorem nativeSubgroup_logarithm_mem_span (Γ : Subgroup G) {g : G} (hg : g ∈ Γ) :
    nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g ∈
      nativeSubgroupRationalLogSpan (E := E) (I := I) Γ :=
  subset_span ⟨g, hg, rfl⟩

omit [Module ℚ E] in
 theorem nativeLieAdjoint_logarithm_conjugation (g h : G) :
    (nativeLieAdjoint (I := I) g : E →L[ℝ] E)
      (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) h) =
        nativeLieGlobalLogarithm (E := E) (I := I) (G := G) (g * h * g⁻¹) := by
  let exp : E → G := fun v => nativeLieExponential (I := I) (G := G) v
  let log : G → E := nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
  let A : E →L[ℝ] E := nativeLieAdjoint (I := I) g
  have hc : g * exp (log h) * g⁻¹ = exp (A (log h)) :=
    nativeLieAdjoint_exponential_conjugation (E := E) (I := I) g (log h)
  have hh : exp (log h) = h := nativeLieExponential_globalLogarithm (E := E) (I := I) (G := G) h
  rw [hh] at hc
  change A (log h) = log (g * h * g⁻¹)
  calc
    _ = log (exp (A (log h))) :=
      (nativeLieGlobalLogarithm_exponential (E := E) (I := I) (G := G) (A (log h))).symm
    _ = _ := congrArg log hc.symm

 theorem nativeSubgroupRationalLogSpan_adjoint_mem (Γ : Subgroup G)
    {g : G} (hg : g ∈ Γ) {w : E}
    (hw : w ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ) :
    (nativeLieAdjoint (I := I) g : E →L[ℝ] E) w ∈
      nativeSubgroupRationalLogSpan (E := E) (I := I) Γ := by
  let S : Submodule ℚ E := nativeSubgroupRationalLogSpan (E := E) (I := I) Γ
  let A : E →ₗ[ℚ] E := (nativeLieAdjoint (I := I) g).toLinearMap.restrictScalars ℚ
  have hle : S ≤ S.comap A := by
    apply Submodule.span_le.mpr
    rintro v ⟨h, hh, rfl⟩
    change (nativeLieAdjoint (I := I) g : E →L[ℝ] E)
      (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) h) ∈ S
    rw [nativeLieAdjoint_logarithm_conjugation]
    exact nativeSubgroup_logarithm_mem_span Γ (Γ.mul_mem (Γ.mul_mem hg hh) (Γ.inv_mem hg))
  exact hle hw

end Hindman168
