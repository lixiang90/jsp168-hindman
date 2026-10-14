import Hindman168.OrderedFlagBasis
import Hindman168.NativeCenterLayerFlagBasis

namespace Hindman168
open Module Submodule
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem native_center_ordered_flag_integer_basis_exists (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    ∃ b : Basis (Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G)))) ℤ
        (nativeCenterLogLattice (I := I) Γ), ∃ t : ℕ → ℕ,
      ∀ j, t j ≤ Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G)) ∧
        (∀ i, ((b i).val.val : E) ∈ nativeLieLowerCentralModel (I := I) (G := G) j ↔ t j ≤ i.val) ∧
        span ℤ (b '' {i | t j ≤ i.val}) = nativeCenterLayerIntegerIntersection (I := I) Γ j := by
  let C := nativeLieCenterModel (I := I) (G := G)
  let L := nativeCenterLogLattice (I := I) Γ
  let P := fun j => nativeCenterLayerIntegerIntersection (I := I) Γ j
  let s := Group.nilpotencyClass G
  have hP : Antitone P := fun i j hij =>
    Submodule.comap_mono (Submodule.restrictScalars_mono ℤ
      (Submodule.comap_mono (nativeLieLowerCentralModel_antitone (I := I) (G := G) hij)))
  obtain ⟨b, t, ht⟩ := ordered_flag_basis_exists (nativeCenterLayerIntegerBasis (I := I) Γ)
    (fun j : Fin (s+1) => P j.val) (fun i j hij => hP hij)
    (fun j => native_center_layer_integer_basis_adapted Γ j.val)
  let u : ℕ → Fin (s+1) := fun j => ⟨min j s, Nat.lt_succ_of_le (min_le_right _ _)⟩
  have he : ∀ j, P j = P (u j).val := by
    intro j
    by_cases hj : j ≤ s
    · simp only [u, min_eq_left hj]
    · have hs : s ≤ j := Nat.le_of_lt (lt_of_not_ge hj)
      have heV : nativeLieLowerCentralModel (I := I) (G := G) j =
          nativeLieLowerCentralModel (I := I) (G := G) s := by
        apply le_antisymm (nativeLieLowerCentralModel_antitone (I := I) (G := G) hs)
        rw [show s = Group.nilpotencyClass G from rfl,
          nativeLieLowerCentralModel_nilpotencyClass_bot]
        exact bot_le
      change integerSubspaceIntersection L ((nativeLieLowerCentralModel (I := I) (G := G) j).comap C.subtype) = _
      rw [heV]
      simp only [P, nativeCenterLayerIntegerIntersection, u, min_eq_right hs]
      rfl
  refine ⟨b, fun j => t (u j), ?_⟩
  intro j
  have h := ht (u j)
  refine ⟨h.1, ?_, ?_⟩
  · intro i
    change b i ∈ P j ↔ _
    rw [he j]
    exact h.2.1 i
  · change span ℤ (b '' {i | t (u j) ≤ i.val}) = P j
    rw [he j]
    exact h.2.2

end Hindman168
