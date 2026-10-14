import Hindman168.NativeLatticeRationalCharacter
import Hindman168.RationalRestrictedKernel

/-! Characters on every original lattice-rational Lie subalgebra.
Separation takes place in the specified lattice's rational form; only
the internal derived layer is annihilated. -/

namespace Hindman168
open Set Submodule
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem nativeRationalSubspace_exists_separating_character
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (V : Submodule ℚ E) (hV : V ≤ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ)
    (hV0 : V ≠ ⊥) (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V) :
    ∃ F : E →ₗ[ℝ] ℝ,
      (∃ v ∈ V, F v ≠ 0) ∧
      (∀ x ∈ span ℝ (V : Set E), ∀ y ∈ span ℝ (V : Set E),
        F (nativeLieAdjointDifferential (I := I) (G := G) x y) = 0) ∧
      (∀ w ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ,
        ∃ q : ℚ, F w = (q : ℝ)) := by
  let W := nativeSubgroupRationalLogSpan (E := E) (I := I) Γ
  let A := nativeLieRationalSubalgebra (I := I) (G := G) V hbr
  let D := nativeLieRationalInternalLayer (I := I) (G := G) V hbr 1
  have hA : Nontrivial A := by
    obtain ⟨v, hv, hv0⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hV0)
    exact ⟨⟨⟨v, hv⟩, 0, fun he => hv0 (congrArg Subtype.val he)⟩⟩
  letI := hA
  have hnil : ∃ k, LieModule.lowerCentralSeries ℚ A A k = ⊥ := by
    refine ⟨Group.nilpotencyClass G, ?_⟩
    apply le_antisymm _ bot_le
    intro x hx
    have hm : x.val ∈ nativeLieRationalInternalLayer (I := I) (G := G) V hbr
        (Group.nilpotencyClass G) := ⟨x, hx, rfl⟩
    rw [nativeLieRationalInternalLayer_nilpotencyClass_bot] at hm
    exact Subtype.ext hm
  obtain ⟨f, hf, hker⟩ := nilpotentLie_exists_nonzero_character hnil
  obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp hf
  have hfa : f a ≠ 0 := by simpa only [LinearMap.zero_apply] using ha
  have hnot : a.val ∉ D := by
    rintro ⟨b, hb, he⟩
    have hba : b = a := Subtype.ext he
    subst b
    exact hfa (hker hb)
  let p : Submodule ℚ W := D.comap W.subtype
  let w : W := ⟨a.val, hV a.property⟩
  obtain ⟨fW, hfw, hp⟩ := Submodule.exists_le_ker_of_notMem (p := p) (v := w) hnot
  letI := nativeLatticeRationalLogSpan_finiteDimensional (E := E) (I := I) Γ
  have hdim : Module.finrank ℚ W = Module.finrank ℝ E :=
    nativeLattice_rationalLogSpan_finrank (E := E) (I := I) Γ
  have hspan : span ℝ (W : Set E) = ⊤ :=
    nativeSubgroupRationalLogSpan_real_span_eq_top (E := E) (I := I) Γ
  let F := rationalSubspaceFunctional W hdim hspan fW
  have hFD : ∀ v ∈ D, F v = 0 := by
    intro v hv
    have hvW : v ∈ W := hV (nativeLieRationalInternalLayer_le V hbr 1 hv)
    have hf0 : fW ⟨v, hvW⟩ = 0 := hp hv
    change rationalSubspaceFunctional W hdim hspan fW (⟨v, hvW⟩ : W) = 0
    rw [rationalSubspaceFunctional_apply, hf0, Rat.cast_zero]
  have hFbr : ∀ x ∈ V, ∀ y ∈ V,
      F (nativeLieAdjointDifferential (I := I) (G := G) x y) = 0 := by
    intro x hx y hy
    apply hFD
    exact nativeLieRationalInternalLayer_differential_next V hbr 0 hx
      (by rw [nativeLieRationalInternalLayer_zero]; exact hy)
  refine ⟨F, ⟨a.val, a.property, ?_⟩, ?_, ?_⟩
  · change rationalSubspaceFunctional W hdim hspan fW w ≠ 0
    rw [rationalSubspaceFunctional_apply]
    exact_mod_cast hfw
  · intro x hx y hy
    exact nativeLieFunctional_kills_brackets_of_rational_span V F hFbr hx hy
  · intro v hv
    exact ⟨fW ⟨v, hv⟩, rationalSubspaceFunctional_apply W hdim hspan fW ⟨v, hv⟩⟩

theorem nativeRationalLieSubalgebra_exists_character
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (hS0 : S ≠ ⊥)
    (hS : nativeLatticeRationalSubspace (E := E) (I := I) Γ (nativeLieSubalgebraModel S)) :
    ∃ F : E →ₗ[ℝ] ℝ,
      (∃ v ∈ nativeLieSubalgebraModel S, F v ≠ 0) ∧
      (∀ x ∈ nativeLieSubalgebraModel S, ∀ y ∈ nativeLieSubalgebraModel S,
        F (nativeLieAdjointDifferential (I := I) (G := G) x y) = 0) ∧
      nativeLatticeRationalSubspace (E := E) (I := I) Γ (nativeLieSubalgebraModel S ⊓ F.ker) ∧
      Module.finrank ℝ (nativeLieSubalgebraModel S ⊓ F.ker : Submodule ℝ E) <
        Module.finrank ℝ (nativeLieSubalgebraModel S) ∧
      (∀ w ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ, ∃ q : ℚ, F w = (q : ℝ)) := by
  let W := nativeSubgroupRationalLogSpan (E := E) (I := I) Γ
  let V : Submodule ℚ E := (nativeLieSubalgebraModel S).restrictScalars ℚ ⊓ W
  have hspan : span ℝ (V : Set E) = nativeLieSubalgebraModel S := hS
  have hV0 : V ≠ ⊥ := by
    intro hz
    apply hS0
    have hs : nativeLieSubalgebraModel S = ⊥ := by
      rw [← hspan, hz]
      simp
    exact SetLike.ext fun x => show x ∈ nativeLieSubalgebraModel S ↔ x = 0 by rw [hs]; rfl
  have hbr : nativeLieRationalBracketClosed (I := I) (G := G) V := by
    intro x y hx hy
    exact ⟨S.lie_mem hx.1 hy.1,
      nativeSubgroupRationalLogSpan_bracket_closed (E := E) (I := I) Γ x y hx.2 hy.2⟩
  obtain ⟨F, ⟨v, hv, hFv⟩, hFbr, hQ⟩ :=
    nativeRationalSubspace_exists_separating_character Γ V inf_le_right hV0 hbr
  refine ⟨F, ⟨v, hv.1, hFv⟩, ?_,
    rationalRestrictedKernel_rational W (nativeLieSubalgebraModel S) F hS hQ,
    restrictedKernel_finrank_lt (nativeLieSubalgebraModel S) F hv.1 hFv, hQ⟩
  simpa only [hspan] using hFbr

theorem nativeLieSubalgebra_character_product_exponentials
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (F : E →ₗ[ℝ] ℝ)
    (hF : ∀ x ∈ nativeLieSubalgebraModel S, ∀ y ∈ nativeLieSubalgebraModel S,
      F (nativeLieAdjointDifferential (I := I) (G := G) x y) = 0)
    {u w : E} (hu : u ∈ nativeLieSubalgebraModel S) (hw : w ∈ nativeLieSubalgebraModel S) :
    F (nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
      (nativeLieExponential (I := I) (G := G) u * nativeLieExponential (I := I) (G := G) w)) =
        F u + F w := by
  let V := (nativeLieSubalgebraModel S).restrictScalars ℚ
  let N := (nativeLieSubalgebraModel S ⊓ F.ker).restrictScalars ℚ
  have hbr : nativeLieRationalBracketClosed (I := I) (G := G) V :=
    fun _ _ hx hy => S.lie_mem hx hy
  have hB : ∀ x ∈ V, ∀ y ∈ V,
      nativeLieAdjointDifferential (I := I) (G := G) x y ∈ N := by
    intro x hx y hy
    refine ⟨?_, hF x hx y hy⟩
    rw [← nativeLieAdjointGenerator_eq_differential]
    exact nativeLieAdjointGenerator_mem_subalgebra S hx hy
  have he := nativeLieGlobalLogarithm_product_rational_layer V V N
    (fun _ hx => hx.1) le_rfl hbr hB hu hw
  have hz := he.2
  change F (_ - (u + w)) = 0 at hz
  rw [map_sub, map_add] at hz
  exact sub_eq_zero.mp hz

theorem nativeLieSubalgebra_character_mul
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (F : E →ₗ[ℝ] ℝ)
    (hF : ∀ x ∈ nativeLieSubalgebraModel S, ∀ y ∈ nativeLieSubalgebraModel S,
      F (nativeLieAdjointDifferential (I := I) (G := G) x y) = 0)
    {g h : G} (hg : g ∈ nativeLieSubalgebraSubgroup (E := E) S)
    (hh : h ∈ nativeLieSubalgebraSubgroup (E := E) S) :
    nativeLieLogarithmCharacter (I := I) (G := G) F (g * h) =
      nativeLieLogarithmCharacter (I := I) (G := G) F g +
        nativeLieLogarithmCharacter (I := I) (G := G) F h := by
  have he := nativeLieSubalgebra_character_product_exponentials S F hF
    ((nativeLieSubalgebraSubgroup_mem_globalLogarithm_iff (E := E) S g).mp hg)
    ((nativeLieSubalgebraSubgroup_mem_globalLogarithm_iff (E := E) S h).mp hh)
  change F (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) (g * h)) =
    F (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g) +
      F (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) h)
  simpa only [nativeLieExponential_globalLogarithm] using he

end Hindman168
