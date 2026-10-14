import Hindman168.NativeRationalSubgroupCharacter

/-! The actual smaller native Lie subalgebra and original group kernel
used in rational-subgroup dimension descent. -/

namespace Hindman168
open Set Submodule
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeLieCharacterKernel
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (F : E →ₗ[ℝ] ℝ)
    (hF : ∀ x ∈ nativeLieSubalgebraModel S, ∀ y ∈ nativeLieSubalgebraModel S,
      F (nativeLieAdjointDifferential (I := I) (G := G) x y) = 0) :
    LieSubalgebra ℝ (GroupLieAlgebra I G) where
  toSubmodule := (nativeLieSubalgebraModel (E := E) S ⊓ F.ker : Submodule ℝ E)
  lie_mem' := by
    intro x y hx hy
    refine ⟨S.lie_mem hx.1 hy.1, ?_⟩
    have he : nativeLieAdjointDifferential (I := I) (G := G) x y =
        (⁅x, y⁆ : GroupLieAlgebra I G) := by
      rw [← nativeLieAdjointGenerator_eq_differential]
      exact nativeLieAdjointGenerator_eq_native_bracket (I := I) (G := G) x y
    exact he ▸ hF x hx.1 y hy.1

omit [Module ℚ E] [Group.IsNilpotent G] [FiniteDimensional ℝ E]
  [ConnectedSpace G] [SimplyConnectedSpace G] in
theorem nativeLieCharacterKernel_model
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (F : E →ₗ[ℝ] ℝ)
    (hF : ∀ x ∈ nativeLieSubalgebraModel S, ∀ y ∈ nativeLieSubalgebraModel S,
      F (nativeLieAdjointDifferential (I := I) (G := G) x y) = 0) :
    nativeLieSubalgebraModel (nativeLieCharacterKernel S F hF) =
      nativeLieSubalgebraModel S ⊓ F.ker := rfl

omit [Module ℚ E] [Group.IsNilpotent G] [FiniteDimensional ℝ E]
  [ConnectedSpace G] [SimplyConnectedSpace G] in
theorem nativeLieCharacterKernel_le
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (F : E →ₗ[ℝ] ℝ)
    (hF : ∀ x ∈ nativeLieSubalgebraModel S, ∀ y ∈ nativeLieSubalgebraModel S,
      F (nativeLieAdjointDifferential (I := I) (G := G) x y) = 0) :
    nativeLieCharacterKernel S F hF ≤ S := fun _ hx => hx.1

omit [Module ℚ E] in
theorem nativeLieCharacterKernel_subgroup_mem_iff
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (F : E →ₗ[ℝ] ℝ)
    (hF : ∀ x ∈ nativeLieSubalgebraModel S, ∀ y ∈ nativeLieSubalgebraModel S,
      F (nativeLieAdjointDifferential (I := I) (G := G) x y) = 0) (g : G) :
    g ∈ nativeLieSubalgebraSubgroup (E := E) (nativeLieCharacterKernel S F hF) ↔
      g ∈ nativeLieSubalgebraSubgroup (E := E) S ∧
        nativeLieLogarithmCharacter (I := I) (G := G) F g = 0 := by
  rw [nativeLieSubalgebraSubgroup_mem_globalLogarithm_iff,
    nativeLieSubalgebraSubgroup_mem_globalLogarithm_iff]
  rfl

theorem nativeRationalLieSubalgebra_character_descent
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (hS0 : S ≠ ⊥)
    (hS : nativeLatticeRationalSubspace (E := E) (I := I) Γ (nativeLieSubalgebraModel S)) :
    ∃ (F : E →ₗ[ℝ] ℝ) (T : LieSubalgebra ℝ (GroupLieAlgebra I G)) (γ : G),
      T ≤ S ∧
      nativeLatticeRationalSubspace (E := E) (I := I) Γ (nativeLieSubalgebraModel T) ∧
      Module.finrank ℝ (nativeLieSubalgebraModel T) < Module.finrank ℝ (nativeLieSubalgebraModel S) ∧
      γ ∈ Γ ∧ γ ∈ nativeLieSubalgebraSubgroup (E := E) S ∧
      nativeLieLogarithmCharacter (I := I) (G := G) F γ ≠ 0 ∧
      (∀ g : G, g ∈ nativeLieSubalgebraSubgroup (E := E) T ↔
        g ∈ nativeLieSubalgebraSubgroup (E := E) S ∧
          nativeLieLogarithmCharacter (I := I) (G := G) F g = 0) ∧
      (∀ g ∈ nativeLieSubalgebraSubgroup (E := E) S,
        ∀ h ∈ nativeLieSubalgebraSubgroup (E := E) S,
          nativeLieLogarithmCharacter (I := I) (G := G) F (g * h) =
            nativeLieLogarithmCharacter (I := I) (G := G) F g +
              nativeLieLogarithmCharacter (I := I) (G := G) F h) := by
  obtain ⟨F, ⟨v, hv, hFv⟩, hF, hrat, hdim, _⟩ :=
    nativeRationalLieSubalgebra_exists_character Γ S hS0 hS
  obtain ⟨γ, hγ, hγS, hγF⟩ :=
    nativeRationalLieSubalgebra_exists_actual_lattice_pivot Γ S hS F hv hFv
  refine ⟨F, nativeLieCharacterKernel S F hF, γ, nativeLieCharacterKernel_le S F hF,
    hrat, hdim, hγ, hγS, hγF, nativeLieCharacterKernel_subgroup_mem_iff S F hF, ?_⟩
  exact fun _ hg _ hh => nativeLieSubalgebra_character_mul S F hF hg hh

end Hindman168
