import Hindman168.NativeLatticeFilteredDiffeomorph
import Hindman168.OrderedFlagDimensions

namespace Hindman168
open Module
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem native_lattice_filtered_layer_start_eq_codimension (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (k : ℕ) :
    nativeLatticeFilteredLayerStart (I := I) Γ k = Module.finrank ℝ E -
      Module.finrank ℝ (nativeLieLowerCentralModel (I := I) (G := G) k) := by
  have hs := native_lattice_filtered_layer_start_spec (I := I) Γ k
  have hd : Module.finrank ℝ (nativeLieLowerCentralModel (I := I) (G := G) k) =
      Module.finrank ℝ E - nativeLatticeFilteredLayerStart (I := I) Γ k := by
    rw [← hs.2.2]
    exact basis_suffix_span_finrank (nativeLatticeFilteredSmoothRealBasis (I := I) Γ) _
  omega

theorem native_lattice_filtered_layer_start_monotone (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    Monotone (nativeLatticeFilteredLayerStart (I := I) Γ) := by
  intro k l hkl
  by_contra h
  have hlk : nativeLatticeFilteredLayerStart (I := I) Γ l <
      nativeLatticeFilteredLayerStart (I := I) Γ k := Nat.lt_of_not_ge h
  have hkn := (native_lattice_filtered_layer_start_spec (I := I) Γ k).1
  let i : Fin (Module.finrank ℝ E) := ⟨nativeLatticeFilteredLayerStart (I := I) Γ l,
    lt_of_lt_of_le hlk hkn⟩
  have hil : nativeLatticeFilteredSmoothRealBasis (I := I) Γ i ∈
      nativeLieLowerCentralModel (I := I) (G := G) l :=
    ((native_lattice_filtered_layer_start_spec (I := I) Γ l).2.1 i).mpr le_rfl
  have hik := nativeLieLowerCentralModel_antitone (I := I) (G := G) hkl hil
  have hi := ((native_lattice_filtered_layer_start_spec (I := I) Γ k).2.1 i).mp hik
  exact Nat.not_le_of_gt hlk hi

theorem native_lattice_filtered_layer_start_zero (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    nativeLatticeFilteredLayerStart (I := I) Γ 0 = 0 := by
  rw [native_lattice_filtered_layer_start_eq_codimension (I := I) Γ,
    nativeLieLowerCentralModel_zero, finrank_top, Nat.sub_self]

theorem native_lattice_filtered_layer_start_nilpotencyClass (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    nativeLatticeFilteredLayerStart (I := I) Γ (Group.nilpotencyClass G) = Module.finrank ℝ E := by
  rw [native_lattice_filtered_layer_start_eq_codimension (I := I) Γ,
    nativeLieLowerCentralModel_nilpotencyClass_bot, finrank_bot, Nat.sub_zero]

end Hindman168
