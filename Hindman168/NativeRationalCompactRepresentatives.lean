import Hindman168.NativeCharacterLatticeReduction
import Mathlib.Topology.Algebra.Monoid

/-! Compact representatives for every rational native Lie subgroup
relative to the SAME specified original lattice. A character kernel
gives strict dimension descent; actual lattice pivots give unit segments. -/

namespace Hindman168
open Set
open scoped Manifold ContDiff Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

def NativeLieCompactRepresentatives (Γ : Subgroup G)
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) : Prop :=
  ∃ K : Set G, IsCompact K ∧ K ⊆ (nativeLieSubalgebraSubgroup (E := E) S : Set G) ∧
    ∀ g ∈ nativeLieSubalgebraSubgroup (E := E) S, ∃ x ∈ K, ∃ γ ∈ Γ, g = x * γ

omit [ConnectedSpace G] [SimplyConnectedSpace G] in
theorem nativeLieCompactRepresentatives_bot (Γ : Subgroup G) :
    NativeLieCompactRepresentatives (E := E) (I := I) Γ ⊥ := by
  refine ⟨{1}, isCompact_singleton, ?_, ?_⟩
  · intro g hg
    rw [mem_singleton_iff] at hg
    subst g
    exact (nativeLieSubalgebraSubgroup (E := E) (⊥ : LieSubalgebra ℝ (GroupLieAlgebra I G))).one_mem
  · rintro g ⟨v, hv, rfl⟩
    change v = 0 at hv
    refine ⟨1, mem_singleton 1, 1, Γ.one_mem, ?_⟩
    subst v
    exact (nativeLieExponential_zero (I := I) (G := G)).trans (one_mul 1).symm

theorem nativeLieCompactRepresentatives_pivot_lift
    (Γ : Subgroup G) (S T : LieSubalgebra ℝ (GroupLieAlgebra I G)) (hTS : T ≤ S)
    (F : E →ₗ[ℝ] ℝ)
    (hker : ∀ g : G, g ∈ nativeLieSubalgebraSubgroup (E := E) T ↔
      g ∈ nativeLieSubalgebraSubgroup (E := E) S ∧
        nativeLieLogarithmCharacter (I := I) (G := G) F g = 0)
    (hmul : ∀ g ∈ nativeLieSubalgebraSubgroup (E := E) S,
      ∀ h ∈ nativeLieSubalgebraSubgroup (E := E) S,
        nativeLieLogarithmCharacter (I := I) (G := G) F (g * h) =
          nativeLieLogarithmCharacter (I := I) (G := G) F g +
            nativeLieLogarithmCharacter (I := I) (G := G) F h)
    (γ : G) (hγ : γ ∈ Γ) (hγS : γ ∈ nativeLieSubalgebraSubgroup (E := E) S)
    (hγF : nativeLieLogarithmCharacter (I := I) (G := G) F γ ≠ 0)
    (hnext : NativeLieCompactRepresentatives (E := E) (I := I) Γ T) :
    NativeLieCompactRepresentatives (E := E) (I := I) Γ S := by
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I (minSmoothness ℝ 3)
  obtain ⟨K, hK, hsub, hrep⟩ := hnext
  let v : E := nativeLieGlobalLogarithm (E := E) (I := I) (G := G) γ
  let a : ℝ → G := fun r => nativeLieExponential (I := I) (G := G) (r • v)
  have ha : Continuous a := (show Continuous (fun w : E =>
    nativeLieExponential (I := I) (G := G) w) from
      nativeLieExponential_continuous (I := I) (G := G)).comp
        (show Continuous (fun r : ℝ => r • v) from continuous_id.smul continuous_const)
  have hv : v ∈ nativeLieSubalgebraModel S :=
    (nativeLieSubalgebraSubgroup_mem_globalLogarithm_iff (E := E) S γ).mp hγS
  have haS : ∀ r, a r ∈ nativeLieSubalgebraSubgroup (E := E) S :=
    fun r => ⟨r • v, (nativeLieSubalgebraModel S).smul_mem r hv, rfl⟩
  have hTSG : nativeLieSubalgebraSubgroup (E := E) T ≤ nativeLieSubalgebraSubgroup (E := E) S := by
    rintro g ⟨w, hw, rfl⟩
    exact ⟨w, hTS hw, rfl⟩
  refine ⟨(a '' Icc 0 1) * K, (isCompact_Icc.image ha).mul hK, ?_, ?_⟩
  · rintro g ⟨b, ⟨r, _, rfl⟩, x, hx, rfl⟩
    exact (nativeLieSubalgebraSubgroup (E := E) S).mul_mem (haS r) (hTSG (hsub hx))
  · intro g hg
    obtain ⟨r, hr, u, hu, z, hz, heq⟩ :=
      nativeCharacter_lattice_reduction Γ S T F hker hmul γ hγ hγS hγF g hg
    obtain ⟨x, hx, η, hη, huEq⟩ := hrep u hu
    refine ⟨a r * x, ⟨a r, ⟨r, hr, rfl⟩, x, hx, rfl⟩,
      η * γ ^ z, Γ.mul_mem hη hz, ?_⟩
    rw [heq, huEq]
    change a r * (x * η) * γ ^ z = a r * x * (η * γ ^ z)
    simp only [mul_assoc]

variable [Module ℚ E]

theorem nativeRationalLieSubalgebra_compact_representatives
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G))
    (hS : nativeLatticeRationalSubspace (E := E) (I := I) Γ (nativeLieSubalgebraModel S)) :
    NativeLieCompactRepresentatives (E := E) (I := I) Γ S := by
  have main : ∀ d : ℕ, ∀ T : LieSubalgebra ℝ (GroupLieAlgebra I G),
      nativeLatticeRationalSubspace (E := E) (I := I) Γ (nativeLieSubalgebraModel T) →
      Module.finrank ℝ (nativeLieSubalgebraModel T) = d →
        NativeLieCompactRepresentatives (E := E) (I := I) Γ T := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro T hT hdim
      by_cases hT0 : T = ⊥
      · subst T
        exact nativeLieCompactRepresentatives_bot Γ
      · obtain ⟨F, U, γ, hUT, hU, hlt, hγ, hγT, hγF, hker, hmul⟩ :=
          nativeRationalLieSubalgebra_character_descent Γ T hT0 hT
        rw [hdim] at hlt
        exact nativeLieCompactRepresentatives_pivot_lift Γ T U hUT F hker hmul γ hγ hγT hγF
          (ih _ hlt U hU rfl)
  exact main _ S hS rfl

end Hindman168
