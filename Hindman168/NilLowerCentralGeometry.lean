import Hindman168.NilClosedLowerCentralFiltration
import Hindman168.NilCompactRootRecipes
import Hindman168.NilCubeLatticeCocompactness

/-! Actual lower-central cube geometry from restricted lattice quotients.
Closedness for the closed series is derived, while cocompactness is still
an explicit geometric input and is not inferred from ambient compactness. -/

namespace Hindman168
open scoped Classical

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [WeaklyLocallyCompactSpace G] {d : ℕ}

theorem nilLowerCentral_cube_compact_from_layer_quotients (Γ : Subgroup G)
    [TopologicalSpace (G ⧸ Γ)] (hπ : Continuous ((↑) : G → G ⧸ Γ))
    (hc : ∀ i, IsClosed (nilLowerCentralFiltration G i : Set G))
    (hquot : ∀ i, CompactSpace ((nilLowerCentralFiltration G i) ⧸
      filtrationLayerLattice (nilLowerCentralFiltration G) Γ i)) :
    IsCompact (cosetCornerCubeSet Γ (upperFaceCubeGroup (nilLowerCentralFiltration G) d)) := by
  exact upperFaceCubeGroup_compact_from_closed_layers (nilLowerCentralFiltration G)
    nilLowerCentralFiltration_conditions Γ hπ hc hquot

theorem nilClosedLowerCentral_cube_compact_from_layer_quotients (Γ : Subgroup G)
    [TopologicalSpace (G ⧸ Γ)] (hπ : Continuous ((↑) : G → G ⧸ Γ))
    (hquot : ∀ i, CompactSpace ((nilClosedLowerCentralFiltration G i) ⧸
      filtrationLayerLattice (nilClosedLowerCentralFiltration G) Γ i)) :
    IsCompact (cosetCornerCubeSet Γ (upperFaceCubeGroup (nilClosedLowerCentralFiltration G) d)) := by
  exact upperFaceCubeGroup_compact_from_closed_layers (nilClosedLowerCentralFiltration G)
    nilClosedLowerCentralFiltration_conditions Γ hπ nilClosedLowerCentralFiltration_isClosed hquot

theorem nilClosedLowerCentral_cubeLattice_compactSpace (Γ : Subgroup G)
    (hquot : ∀ i, CompactSpace ((nilClosedLowerCentralFiltration G i) ⧸
      filtrationLayerLattice (nilClosedLowerCentralFiltration G) Γ i)) :
    CompactSpace ((upperFaceCubeGroup (nilClosedLowerCentralFiltration G) d) ⧸
      upperFaceCubeLattice (nilClosedLowerCentralFiltration G) Γ d) := by
  exact upperFaceCubeLattice_compactSpace_from_layer_quotients (nilClosedLowerCentralFiltration G)
    nilClosedLowerCentralFiltration_conditions Γ
    (closedFiltrationLayers_weaklyLocallyCompact _ nilClosedLowerCentralFiltration_isClosed) hquot

omit [WeaklyLocallyCompactSpace G] in
theorem nilClosedLowerCentral_cubeGroup_eq_of_closed_layers
    (hc : ∀ i, IsClosed (nilLowerCentralFiltration G i : Set G)) :
    upperFaceCubeGroup (nilClosedLowerCentralFiltration G) d =
      upperFaceCubeGroup (nilLowerCentralFiltration G) d := by
  have he : nilClosedLowerCentralFiltration G = nilLowerCentralFiltration G :=
    funext (fun i => nilClosedLowerCentralFiltration_eq_of_isClosed i (hc i))
  rw [he]

omit [IsTopologicalGroup G] [WeaklyLocallyCompactSpace G] in
theorem nilLowerCentral_finite_closed_layers [T1Space G] [Group.IsNilpotent G]
    {s : ℕ} (hs : Group.nilpotencyClass G ≤ s)
    (hc : ∀ i, i ≤ s → IsClosed (nilLowerCentralFiltration G i : Set G)) :
    ∀ i, IsClosed (nilLowerCentralFiltration G i : Set G) := by
  intro i
  by_cases hi : i ≤ s
  · exact hc i hi
  · have hb := nilLowerCentralFiltration_beyond_terminal hs (by omega : s+1 ≤ i)
    rw [hb]
    exact isClosed_singleton

omit [IsTopologicalGroup G] [WeaklyLocallyCompactSpace G] in
theorem nilLowerCentral_finite_layer_quotients [Group.IsNilpotent G]
    {s : ℕ} (hs : Group.nilpotencyClass G ≤ s) (Γ : Subgroup G)
    (hq : ∀ i, i ≤ s → CompactSpace ((nilLowerCentralFiltration G i) ⧸
      filtrationLayerLattice (nilLowerCentralFiltration G) Γ i)) :
    ∀ i, CompactSpace ((nilLowerCentralFiltration G i) ⧸
      filtrationLayerLattice (nilLowerCentralFiltration G) Γ i) := by
  intro i
  by_cases hi : i ≤ s
  · exact hq i hi
  · have hb := nilLowerCentralFiltration_beyond_terminal hs (by omega : s+1 ≤ i)
    letI : Subsingleton (nilLowerCentralFiltration G i) := by
      rw [hb]
      infer_instance
    infer_instance

omit [WeaklyLocallyCompactSpace G] in
theorem nilClosedLowerCentral_finite_layer_quotients [T1Space G] [Group.IsNilpotent G]
    {s : ℕ} (hs : Group.nilpotencyClass G ≤ s) (Γ : Subgroup G)
    (hq : ∀ i, i ≤ s → CompactSpace ((nilClosedLowerCentralFiltration G i) ⧸
      filtrationLayerLattice (nilClosedLowerCentralFiltration G) Γ i)) :
    ∀ i, CompactSpace ((nilClosedLowerCentralFiltration G i) ⧸
      filtrationLayerLattice (nilClosedLowerCentralFiltration G) Γ i) := by
  intro i
  by_cases hi : i ≤ s
  · exact hq i hi
  · have hb := nilClosedLowerCentralFiltration_beyond_terminal hs (by omega : s+1 ≤ i)
    letI : Subsingleton (nilClosedLowerCentralFiltration G i) := by
      rw [hb]
      infer_instance
    infer_instance

end Hindman168
