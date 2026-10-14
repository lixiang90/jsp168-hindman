import Hindman168.NativeRationalLieSubgroupSpan
import Hindman168.NativeLieLogarithmCharacter
import Hindman168.RationalSubspaceFunctional
import Hindman168.NilpotentLieCharacter

/-! Rational real characters for the original specified lattice. The
real extension kills brackets by two span inductions; the original BCH
identity then gives additivity on the original group. -/

namespace Hindman168
open Set Submodule
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

omit [CompleteSpace E] [LieGroup I ∞ G] [BoundarylessManifold I G]
  [T2Space G] [Group.IsNilpotent G] [FiniteDimensional ℝ E]
  [ConnectedSpace G] [SimplyConnectedSpace G] in
theorem nativeLieFunctional_kills_brackets_of_rational_span
    (V : Submodule ℚ E) (F : E →ₗ[ℝ] ℝ)
    (hF : ∀ x ∈ V, ∀ y ∈ V,
      F (nativeLieAdjointDifferential (I := I) (G := G) x y) = 0)
    {x y : E} (hx : x ∈ span ℝ (V : Set E)) (hy : y ∈ span ℝ (V : Set E)) :
    F (nativeLieAdjointDifferential (I := I) (G := G) x y) = 0 := by
  let B := nativeLieAdjointDifferential (I := I) (G := G)
  have hs : ∀ v ∈ V, ∀ w ∈ span ℝ (V : Set E), B v w ∈ F.ker := by
    intro v hv w hw
    have hle : span ℝ (V : Set E) ≤ F.ker.comap (B v).toLinearMap := by
      apply span_le.mpr
      exact fun z hz => hF v hv z hz
    exact hle hw
  have hle : span ℝ (V : Set E) ≤ F.ker.comap (B.flip y).toLinearMap := by
    apply span_le.mpr
    exact fun v hv => hs v hv y hy
  exact hle hx

omit [Module ℚ E] [Group.IsNilpotent G] [FiniteDimensional ℝ E]
  [ConnectedSpace G] [SimplyConnectedSpace G] in
theorem nativeLieFunctional_lowerCentral_le_kernel
    (F : E →ₗ[ℝ] ℝ)
    (hF : ∀ x y : E, F (nativeLieAdjointDifferential (I := I) (G := G) x y) = 0) :
    nativeLieLowerCentralModel (I := I) (G := G) 1 ≤ F.ker := by
  unfold nativeLieLowerCentralModel
  rw [show 1 = 0 + 1 from rfl, LieModule.lowerCentralSeries_succ,
    LieSubmodule.lieIdeal_oper_eq_linear_span']
  apply span_le.mpr
  rintro z ⟨x, _, y, _, rfl⟩
  have he : nativeLieAdjointDifferential (I := I) (G := G) x y =
      (⁅x, y⁆ : GroupLieAlgebra I G) := by
    rw [← nativeLieAdjointGenerator_eq_differential]
    exact nativeLieAdjointGenerator_eq_native_bracket (I := I) (G := G) x y
  exact he ▸ hF x y

theorem nativeLattice_exists_rational_character [Nontrivial E]
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    ∃ F : E →ₗ[ℝ] ℝ, F ≠ 0 ∧
      nativeLieLowerCentralModel (I := I) (G := G) 1 ≤ F.ker ∧
      nativeLatticeRationalSubspace (E := E) (I := I) Γ F.ker ∧
      (∀ w ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ,
        ∃ q : ℚ, F w = (q : ℝ)) := by
  let W := nativeSubgroupRationalLogSpan (E := E) (I := I) Γ
  let hbr := nativeSubgroupRationalLogSpan_bracket_closed (E := E) (I := I) Γ
  let A := nativeLieRationalSubalgebra (I := I) (G := G) W hbr
  letI := nativeLatticeRationalLogSpan_finiteDimensional (E := E) (I := I) Γ
  have hspan : span ℝ (W : Set E) = ⊤ :=
    nativeSubgroupRationalLogSpan_real_span_eq_top (E := E) (I := I) Γ
  have hdim : Module.finrank ℚ W = Module.finrank ℝ E :=
    nativeLattice_rationalLogSpan_finrank (E := E) (I := I) Γ
  have hW : W ≠ ⊥ := by
    intro hz
    simp [hz] at hspan
  have hA : Nontrivial A := by
    obtain ⟨w, hw, hw0⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hW)
    exact ⟨⟨⟨w, hw⟩, 0, fun he => hw0 (congrArg Subtype.val he)⟩⟩
  letI := hA
  have hnil : ∃ k, LieModule.lowerCentralSeries ℚ A A k = ⊥ := by
    refine ⟨Group.nilpotencyClass G, ?_⟩
    apply le_antisymm _ bot_le
    intro x hx
    have hm : x.val ∈ nativeLieRationalInternalLayer (I := I) (G := G) W hbr
        (Group.nilpotencyClass G) := ⟨x, hx, rfl⟩
    rw [nativeLieRationalInternalLayer_nilpotencyClass_bot] at hm
    change x.val = 0 at hm
    exact Subtype.ext hm
  obtain ⟨f, hf, hker⟩ := nilpotentLie_exists_nonzero_character hnil
  let fW : W →ₗ[ℚ] ℚ := f
  let F := rationalSubspaceFunctional W hdim hspan fW
  have hFbr : ∀ x ∈ W, ∀ y ∈ W,
      F (nativeLieAdjointDifferential (I := I) (G := G) x y) = 0 := by
    intro x hx y hy
    let a : A := ⟨x, hx⟩
    let b : A := ⟨y, hy⟩
    have he : nativeLieAdjointDifferential (I := I) (G := G) x y =
        (⁅a, b⁆ : A).val := by
      rw [← nativeLieAdjointGenerator_eq_differential]
      exact nativeLieAdjointGenerator_eq_native_bracket (I := I) (G := G) x y
    rw [he]
    change rationalSubspaceFunctional W hdim hspan fW (⟨(⁅a, b⁆ : A).val,
      (⁅a, b⁆ : A).property⟩ : W) = 0
    rw [rationalSubspaceFunctional_apply]
    change (f ⁅a, b⁆ : ℝ) = 0
    rw [lieCharacter_bracket_eq_zero f hker, Rat.cast_zero]
  refine ⟨F, rationalSubspaceFunctional_ne_zero W hdim hspan fW hf, ?_,
    rationalSubspaceFunctional_kernel_rational W hdim hspan fW, ?_⟩
  · apply nativeLieFunctional_lowerCentral_le_kernel
    intro x y
    exact nativeLieFunctional_kills_brackets_of_rational_span W F hFbr
      (hspan ▸ trivial) (hspan ▸ trivial)
  · intro w hw
    exact ⟨fW ⟨w, hw⟩, rationalSubspaceFunctional_apply W hdim hspan fW ⟨w, hw⟩⟩

theorem nativeLattice_exists_rational_character_with_pivot [Nontrivial E]
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    ∃ F : E →ₗ[ℝ] ℝ, F ≠ 0 ∧
      nativeLatticeRationalSubspace (E := E) (I := I) Γ F.ker ∧
      Module.finrank ℝ F.ker < Module.finrank ℝ E ∧
      Function.Surjective (nativeLieLogarithmCharacter (I := I) (G := G) F) ∧
      (∀ g h : G, nativeLieLogarithmCharacter (I := I) (G := G) F (g * h) =
        nativeLieLogarithmCharacter (I := I) (G := G) F g +
          nativeLieLogarithmCharacter (I := I) (G := G) F h) ∧
      (∀ γ ∈ Γ, ∃ q : ℚ, nativeLieLogarithmCharacter (I := I) (G := G) F γ = (q : ℝ)) ∧
      (∃ γ ∈ Γ, nativeLieLogarithmCharacter (I := I) (G := G) F γ ≠ 0) := by
  obtain ⟨F, hF, hcomm, hrat, hQ⟩ :=
    nativeLattice_exists_rational_character (E := E) (I := I) Γ
  refine ⟨F, hF, hrat, Submodule.finrank_lt (fun h => hF (LinearMap.ker_eq_top.mp h)),
    nativeLieLogarithmCharacter_surjective F hF,
    nativeLieLogarithmCharacter_mul F hcomm, ?_, ?_⟩
  · intro γ hγ
    exact hQ _ (nativeSubgroup_logarithm_mem_span Γ hγ)
  · by_contra hn
    push Not at hn
    apply hF
    apply nativeLieLogarithmFunctional_eq_zero_of_compact_quotient (E := E) (I := I) Γ F hcomm
    exact hn

end Hindman168
