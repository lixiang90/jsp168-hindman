import Hindman168.NativeSpanningSubgroupRationalHull

namespace Hindman168
open Set Submodule
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

/-! Rational character descent still works when each original lattice
pivot has some positive power in the specified subgroup. Every reducing
element is taken in that specified subgroup. -/

theorem nativeRationalLieSubalgebra_root_compact_representatives
    (Γ K : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G))
    (hS : nativeLatticeRationalSubspace (E := E) (I := I) Γ (nativeLieSubalgebraModel S))
    (hroot : Γ ⊓ nativeLieSubalgebraSubgroup (E := E) S ≤
      nativeSubgroupRationalHull (E := E) (I := I) K) :
    NativeLieCompactRepresentatives (E := E) (I := I) K S := by
  have main : ∀ d : ℕ, ∀ T : LieSubalgebra ℝ (GroupLieAlgebra I G),
      nativeLatticeRationalSubspace (E := E) (I := I) Γ (nativeLieSubalgebraModel T) →
      (Γ ⊓ nativeLieSubalgebraSubgroup (E := E) T ≤ nativeSubgroupRationalHull (E := E) (I := I) K) →
      Module.finrank ℝ (nativeLieSubalgebraModel T) = d →
      NativeLieCompactRepresentatives (E := E) (I := I) K T := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro T hT hTK hdim
      by_cases hT0 : T = ⊥
      · subst T
        exact nativeLieCompactRepresentatives_bot K
      · obtain ⟨F, U, γ, hUT, hU, hlt, hγ, hγT, hγF, hker, hmul⟩ :=
          nativeRationalLieSubalgebra_character_descent Γ T hT0 hT
        obtain ⟨n, hn, hpow⟩ := (nativeSubgroupRationalHull_mem_iff_positive_power K γ).mp
          (hTK ⟨hγ, hγT⟩)
        have hpowT := (nativeLieSubalgebraSubgroup (E := E) T).pow_mem hγT n
        have hpowF : nativeLieLogarithmCharacter (I := I) (G := G) F (γ ^ n) ≠ 0 := by
          change F (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) (γ ^ n)) ≠ 0
          rw [nativeLieGlobalLogarithm_pow, map_smul]
          exact mul_ne_zero (by exact_mod_cast hn.ne') hγF
        have hUK : Γ ⊓ nativeLieSubalgebraSubgroup (E := E) U ≤
            nativeSubgroupRationalHull (E := E) (I := I) K := by
          intro g hg
          apply hTK
          refine ⟨hg.1, ?_⟩
          obtain ⟨v, hv, rfl⟩ := hg.2
          exact ⟨v, hUT hv, rfl⟩
        rw [hdim] at hlt
        exact nativeLieCompactRepresentatives_pivot_lift K T U hUT F hker hmul
          (γ ^ n) hpow hpowT hpowF (ih _ hlt U hU hUK rfl)
  exact main _ S hS hroot rfl

theorem nativeSpanningSubgroup_compact_representatives
    (Γ K : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (hK : K ≤ Γ)
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G))
    (hspan : span ℝ ((nativeLieGlobalLogarithm (E := E) (I := I) (G := G)) '' (K : Set G)) =
      nativeLieSubalgebraModel (E := E) S) :
    NativeLieCompactRepresentatives (E := E) (I := I) K S :=
  nativeRationalLieSubalgebra_root_compact_representatives Γ K S
    (nativeSubgroup_logSpan_rational Γ K hK _ hspan)
    (nativeSubgroup_logSpan_covers_lattice_roots Γ K hK S hspan)

theorem nativeSpanningSubgroup_quotient_compact
    (Γ K : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (hK : K ≤ Γ)
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G))
    (hspan : span ℝ ((nativeLieGlobalLogarithm (E := E) (I := I) (G := G)) '' (K : Set G)) =
      nativeLieSubalgebraModel (E := E) S) :
    CompactSpace (nativeLieSubalgebraSubgroup (E := E) S ⧸
      K.comap (nativeLieSubalgebraSubgroup (E := E) S).subtype) := by
  obtain ⟨C, hC, hsub, hrep⟩ := nativeSpanningSubgroup_compact_representatives Γ K hK S hspan
  let L := nativeLieSubalgebraSubgroup (E := E) S
  let CL : Set L := ((↑) : L → G) ⁻¹' C
  have hCR : C ⊆ Set.range ((↑) : L → G) := fun x hx => ⟨⟨x, hsub hx⟩, rfl⟩
  have hCL : IsCompact CL := Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hC hCR
  apply compactSpace_of_lattice_representatives (K.comap L.subtype) CL hCL
  intro g
  obtain ⟨x, hx, γ, hγ, heq⟩ := hrep g.val g.property
  have hγL : γ ∈ L := by
    have he : γ = x⁻¹ * g.val := by rw [heq]; simp only [inv_mul_cancel_left]
    rw [he]
    exact L.mul_mem (L.inv_mem (hsub hx)) g.property
  exact ⟨⟨x, hsub hx⟩, hx, ⟨γ, hγL⟩, hγ, Subtype.ext heq⟩

end Hindman168

