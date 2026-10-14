import Hindman168.NativeSubgroupBracketSpan
import Hindman168.NativeLieRationalAdjoint

/-! A genuine rational exponential hull for an arbitrary specified
original subgroup. Original integer conjugations have already proved
bracket closure of its logarithmic rational span, so this hull requires
no supplied rational Lie structure or assumed BCH law. -/

namespace Hindman168
open Function Set Submodule
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeSubgroupRationalHull (Γ : Subgroup G) : Subgroup G :=
  nativeLieRationalExponentialSubgroup
    (nativeSubgroupRationalLogSpan (E := E) (I := I) Γ)
    (nativeSubgroupRationalLogSpan_bracket_closed (E := E) (I := I) Γ)

 theorem nativeSubgroupRationalHull_mem_iff (Γ : Subgroup G) (g : G) :
    g ∈ nativeSubgroupRationalHull (E := E) (I := I) Γ ↔
      nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g ∈
        nativeSubgroupRationalLogSpan (E := E) (I := I) Γ :=
  nativeLieRationalExponentialSubgroup_mem_logarithm_iff _ _ g

 theorem nativeSubgroup_le_rationalHull (Γ : Subgroup G) :
    Γ ≤ nativeSubgroupRationalHull (E := E) (I := I) Γ := by
  intro g hg
  exact (nativeSubgroupRationalHull_mem_iff Γ g).mpr
    (nativeSubgroup_logarithm_mem_span (E := E) (I := I) Γ hg)

 theorem nativeSubgroupRationalLogSpan_le_of_logarithms_mem (Γ : Subgroup G)
    (V : Submodule ℚ E)
    (h : ∀ g ∈ Γ, nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g ∈ V) :
    nativeSubgroupRationalLogSpan (E := E) (I := I) Γ ≤ V := by
  apply span_le.mpr
  rintro v ⟨g, hg, rfl⟩
  exact h g hg

 theorem nativeSubgroupRationalHull_le_of_logarithms_mem (Γ : Subgroup G)
    (V : Submodule ℚ E) (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V)
    (h : ∀ g ∈ Γ, nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g ∈ V) :
    nativeSubgroupRationalHull (E := E) (I := I) Γ ≤
      nativeLieRationalExponentialSubgroup (I := I) (G := G) V hbr := by
  intro g hg
  apply (nativeLieRationalExponentialSubgroup_mem_logarithm_iff V hbr g).mpr
  exact nativeSubgroupRationalLogSpan_le_of_logarithms_mem Γ V h
    ((nativeSubgroupRationalHull_mem_iff Γ g).mp hg)

 theorem nativeSubgroupRationalHull_adjoint_mem (Γ : Subgroup G) {g : G}
    (hg : g ∈ nativeSubgroupRationalHull (E := E) (I := I) Γ) {w : E}
    (hw : w ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ) :
    (nativeLieAdjoint (I := I) g : E →L[ℝ] E) w ∈
      nativeSubgroupRationalLogSpan (E := E) (I := I) Γ :=
  nativeLieAdjoint_mem_rational_of_logarithm _
    (nativeSubgroupRationalLogSpan_bracket_closed Γ) g
    ((nativeSubgroupRationalHull_mem_iff Γ g).mp hg) hw

end Hindman168
