import Hindman168.NativeSubgroupRealLieSpan
import Hindman168.NilpotentLieSubalgebraSpanning
import Hindman168.NativeLieCharacterCompactQuotient
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Logarithms of any actual cocompact subgroup of the original connected
simply connected nilpotent Lie group span its entire original real model.
A proper native Lie subalgebra remains proper after adding the actual
commutator layer; real dual separation yields a genuine surjective real
character on the actual compact coset quotient, a contradiction. -/

namespace Hindman168
open Function Set Submodule
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieSubalgebra_eq_top_of_compact_quotient (Γ : Subgroup G)
    [CompactSpace (G ⧸ Γ)] (S : LieSubalgebra ℝ (GroupLieAlgebra I G))
    (hΓ : ∀ g ∈ Γ, nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g ∈
      nativeLieSubalgebraModel (E := E) S) : S = ⊤ := by
  by_contra hS
  let T : Submodule ℝ E := nativeLieSubalgebraModel (E := E) S ⊔
    nativeLieLowerCentralModel (I := I) (G := G) 1
  have hT : T ≠ ⊤ := nilpotentLieSubalgebra_sup_commutator_ne_top S
    ⟨Group.nilpotencyClass G, nativeLieLowerCentral_nilpotencyClass_bot (I := I) (G := G)⟩ hS
  obtain ⟨f, hf, hker⟩ := T.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hT)
  have hcomm : nativeLieLowerCentralModel (I := I) (G := G) 1 ≤ f.ker :=
    fun _ hv => hker (mem_sup_right hv)
  have hz : ∀ g ∈ Γ, f (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g) = 0 :=
    fun g hg => hker (mem_sup_left (hΓ g hg))
  exact hf (nativeLieLogarithmFunctional_eq_zero_of_compact_quotient (E := E) (I := I) Γ f hcomm hz)

variable [Module ℚ E]

 theorem nativeSubgroupRealLieSpan_eq_top_of_compact_quotient (Γ : Subgroup G)
    [CompactSpace (G ⧸ Γ)] : nativeSubgroupRealLieSpan (E := E) (I := I) Γ = ⊤ := by
  apply nativeLieSubalgebra_eq_top_of_compact_quotient (E := E) (I := I) Γ
  intro g hg
  change nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g ∈
    span ℝ (nativeSubgroupRationalLogSpan (E := E) (I := I) Γ : Set E)
  exact subset_span (nativeSubgroup_logarithm_mem_span (E := E) (I := I) Γ hg)

 theorem nativeSubgroupRationalLogSpan_real_span_eq_top (Γ : Subgroup G)
    [CompactSpace (G ⧸ Γ)] :
    span ℝ (nativeSubgroupRationalLogSpan (E := E) (I := I) Γ : Set E) = ⊤ := by
  have hs := nativeSubgroupRealLieSpan_eq_top_of_compact_quotient (E := E) (I := I) Γ
  exact congrArg (fun S : LieSubalgebra ℝ (GroupLieAlgebra I G) => S.toSubmodule) hs

 theorem nativeSubgroup_logarithms_real_span_eq_top (Γ : Subgroup G)
    [CompactSpace (G ⧸ Γ)] :
    span ℝ ((nativeLieGlobalLogarithm (E := E) (I := I) (G := G)) '' (Γ : Set G)) = ⊤ := by
  rw [← nativeSubgroupRationalLogSpan_real_span_eq (E := E) (I := I) Γ]
  exact nativeSubgroupRationalLogSpan_real_span_eq_top (E := E) (I := I) Γ

end Hindman168
