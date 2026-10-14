import Hindman168.NativeSubgroupRationalRootInduction
import Hindman168.NilpotentArbitraryPositiveRoots
import Hindman168.NativePositiveRootsRationalHull

/-! The actual rational exponential hull of the ORIGINAL specified
subgroup equals its genuine positive-root subgroup. The noncommuting
root subgroup theorem and the terminating internal Lie-layer induction
prove both inclusions, without extra subgroup hypotheses. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeSubgroupRationalHull_le_positiveRoots (Γ : Subgroup G) :
    nativeSubgroupRationalHull (E := E) (I := I) Γ ≤ nilpotentArbitraryPositiveRootSubgroup Γ :=
  nativeSubgroupRationalHull_le_root_closed Γ _
    (nilpotentArbitraryPositiveRootSubgroup_contains Γ)
    (fun _ _ hn hp => nilpotentArbitraryPositiveRootSubgroup_root Γ hn hp)

 theorem nativeSubgroupRationalHull_eq_positiveRoots (Γ : Subgroup G) :
    nativeSubgroupRationalHull (E := E) (I := I) Γ = nilpotentArbitraryPositiveRootSubgroup Γ :=
  le_antisymm (nativeSubgroupRationalHull_le_positiveRoots Γ)
    (positiveSubgroupRoots_le_nativeRationalHull Γ)

 theorem nativeSubgroupRationalHull_mem_iff_positive_power (Γ : Subgroup G) (g : G) :
    g ∈ nativeSubgroupRationalHull (E := E) (I := I) Γ ↔
      ∃ n : ℕ, 0 < n ∧ g ^ n ∈ Γ := by
  rw [nativeSubgroupRationalHull_eq_positiveRoots]
  exact Iff.rfl

 theorem nativeSubgroupRationalLogSpan_mem_iff_positive_power (Γ : Subgroup G) (v : E) :
    v ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ ↔
      ∃ n : ℕ, 0 < n ∧ nativeLieExponential (I := I) (G := G) v ^ n ∈ Γ := by
  have he := (nativeSubgroupRationalHull_mem_iff (E := E) (I := I) Γ
    (nativeLieExponential (I := I) (G := G) v)).symm.trans
    (nativeSubgroupRationalHull_mem_iff_positive_power (E := E) (I := I) Γ
      (nativeLieExponential (I := I) (G := G) v))
  simpa only [nativeLieGlobalLogarithm_exponential] using he

 theorem nativeSubgroupRationalHull_eq_self_of_root_closed (Γ : Subgroup G)
    (hroot : ∀ (g : G) (n : ℕ), 0 < n → g ^ n ∈ Γ → g ∈ Γ) :
    nativeSubgroupRationalHull (E := E) (I := I) Γ = Γ :=
  le_antisymm (nativeSubgroupRationalHull_le_root_closed Γ Γ le_rfl hroot)
    (nativeSubgroup_le_rationalHull Γ)

 theorem nativeSubgroupRationalHull_uniform_power_of_fg (Γ K : Subgroup G)
    (hK : K.FG) (hKΓ : K ≤ nativeSubgroupRationalHull (E := E) (I := I) Γ) :
    ∃ n : ℕ, 0 < n ∧ ∀ g ∈ K, g ^ n ∈ Γ := by
  apply nilpotent_arbitrary_roots_uniform_of_fg Γ K hK
  intro g hg
  exact nativeSubgroupRationalHull_le_positiveRoots Γ (hKΓ hg)

end Hindman168
