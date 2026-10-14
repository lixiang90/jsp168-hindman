import Hindman168.NativeCentralLayerKernel
import Hindman168.NativeLieLayerLatticeCompact
import Hindman168.FiniteRealQuotientDimension

/-! An actual last nonzero lower-central layer is a rational central
subspace contained in every earlier layer and strictly reduces dimension. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

omit [Module ℚ E] [ConnectedSpace G] [SimplyConnectedSpace G] [FiniteDimensional ℝ E] in
theorem nativeLieLowerCentralModel_last_nonzero_exists [Nontrivial E] :
    ∃ j : ℕ, nativeLieLowerCentralModel (I := I) (G := G) j ≠ ⊥ ∧
      nativeLieLowerCentralModel (I := I) (G := G) (j+1) = ⊥ := by
  classical
  have hex : ∃ n, nativeLieLowerCentralModel (I := I) (G := G) n = ⊥ :=
    ⟨Group.nilpotencyClass G, nativeLieLowerCentralModel_nilpotencyClass_bot⟩
  have hn : Nat.find hex ≠ 0 := by
    intro h
    have he := Nat.find_spec hex
    rw [h, nativeLieLowerCentralModel_zero] at he
    exact top_ne_bot he
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hn
  refine ⟨j, Nat.find_min hex (by omega), ?_⟩
  simpa only [hj, Nat.succ_eq_add_one] using Nat.find_spec hex

theorem nativeLattice_terminal_central_subspace_exists [Nontrivial E] (Γ : Subgroup G)
    [CompactSpace (G ⧸ Γ)] :
    ∃ j : ℕ,
      nativeLieLowerCentralModel (I := I) (G := G) j ≠ ⊥ ∧
      nativeLieLowerCentralModel (I := I) (G := G) (j+1) = ⊥ ∧
      nativeLieLowerCentralModel (I := I) (G := G) j ≤ nativeLieCenterModel (I := I) (G := G) ∧
      nativeLatticeRationalSubspace (E := E) (I := I) Γ
        (nativeLieLowerCentralModel (I := I) (G := G) j) ∧
      (∀ k ≤ j, nativeLieLowerCentralModel (I := I) (G := G) j ≤
        nativeLieLowerCentralModel (I := I) (G := G) k) ∧
      Module.finrank ℝ (E ⧸ nativeLieLowerCentralModel (I := I) (G := G) j) <
        Module.finrank ℝ E := by
  obtain ⟨j, hj, hnext⟩ := nativeLieLowerCentralModel_last_nonzero_exists (I := I) (G := G)
  exact ⟨j, hj, hnext, nativeLieLowerCentralModel_le_center_of_next_bot j hnext,
    nativeLieLowerCentralModel_lattice_rational Γ j,
    fun _ hk => nativeLieLowerCentralModel_antitone hk,
    finiteRealQuotient_finrank_lt_of_ne_bot _ hj⟩

end Hindman168
