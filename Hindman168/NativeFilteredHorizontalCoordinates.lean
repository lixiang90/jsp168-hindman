import Hindman168.NativeFilteredHorizontalSize
import Hindman168.NativeFilteredLogLayerCoordinates

namespace Hindman168
open Module
open scoped Classical BigOperators Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeFilteredHorizontalCoordinates (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (g : G) :
    ↥(nativeFilteredHorizontalIndices (I := I) Γ) → ℝ :=
  fun i => (nativeLatticeFilteredSmoothRealBasis (I := I) Γ).repr
    (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g) i.val

theorem native_filtered_horizontal_coord_functional (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (i : ↥(nativeFilteredHorizontalIndices (I := I) Γ)) :
    nativeLieLowerCentralModel (I := I) (G := G) 1 ≤
      ((nativeLatticeFilteredSmoothRealBasis (I := I) Γ).coord i.val).ker := by
  apply (native_filtered_horizontal_iff_tail_zero (I := I) Γ _).mpr
  intro j hj
  have hi := (native_filtered_horizontal_indices_mem_iff (I := I) Γ i.val).mp i.property
  have hji : j ≠ i.val := by intro he; subst j; omega
  simp only [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, if_neg hji]

theorem native_filtered_horizontal_coordinates_diffeomorph (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (x : Fin (Module.finrank ℝ E) → ℝ) :
    nativeFilteredHorizontalCoordinates (I := I) Γ (nativeLatticeFilteredDiffeomorph (I := I) Γ x) =
      fun i => x i.val := by
  funext i
  change (nativeLatticeFilteredSmoothRealBasis (I := I) Γ).repr
    (nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
      (nativeLatticeFilteredDiffeomorph (I := I) Γ x)) i.val = x i.val
  have h := native_filtered_smooth_basis_character_evaluation (I := I) Γ
    ((nativeLatticeFilteredSmoothRealBasis (I := I) Γ).coord i.val)
    (native_filtered_horizontal_coord_functional (I := I) Γ i) x
  change (nativeLatticeFilteredSmoothRealBasis (I := I) Γ).repr
    (nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
      (nativeLatticeFilteredDiffeomorph (I := I) Γ x)) i.val = _ at h
  simpa only [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] using h

theorem native_filtered_horizontal_coordinates_mul (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (g h : G) :
    nativeFilteredHorizontalCoordinates (I := I) Γ (g*h) =
      nativeFilteredHorizontalCoordinates (I := I) Γ g + nativeFilteredHorizontalCoordinates (I := I) Γ h := by
  funext i
  exact nativeLieLogarithmCharacter_mul
    ((nativeLatticeFilteredSmoothRealBasis (I := I) Γ).coord i.val)
    (native_filtered_horizontal_coord_functional (I := I) Γ i) g h

theorem native_filtered_horizontal_coordinates_ker (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (g : G) :
    nativeFilteredHorizontalCoordinates (I := I) Γ g = 0 ↔
      g ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := by
  rw [native_filtered_group_layer_mem_iff_log_coordinates (I := I) Γ]
  constructor
  · intro h i hi
    have hs := congrFun h ⟨i, (native_filtered_horizontal_indices_mem_iff (I := I) Γ i).mpr hi⟩
    exact hs
  · intro h
    funext i
    exact h i.val ((native_filtered_horizontal_indices_mem_iff (I := I) Γ i.val).mp i.property)

theorem native_filtered_horizontal_coordinates_continuous (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    Continuous (nativeFilteredHorizontalCoordinates (I := I) Γ) := by
  apply continuous_pi
  intro i
  exact ((nativeLatticeFilteredSmoothRealBasis (I := I) Γ).coord i.val).continuous_of_finiteDimensional.comp
    (nativeLieGlobalLogarithm (E := E) (I := I) (G := G)).continuous

end Hindman168
