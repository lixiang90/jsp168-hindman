import Hindman168.NativeCenterCoordinateExtension
import Hindman168.NativeCenterLatticeIndependent
import Hindman168.NativeOrderedCoordinateAppend

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [Module ℚ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem native_center_ordered_basis_extension (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (m : ℕ) :
    letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
    letI := nativeCenterQuotient_t2Space (I := I) (G := G)
    letI := nativeCenterQuotient_lieGroup (I := I) (G := G)
    letI := nativeCenterQuotient_simplyConnected (I := I) (G := G)
    let F := E ⧸ nativeLieCenterModel (I := I) (G := G)
    let Q := G ⧸ Subgroup.center G
    let nc := Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G))
    ∀ v : Fin m → F,
      (∀ i, nativeLieExponential (I := 𝓘(ℝ, F)) (G := Q) (v i) ∈
        Γ.map (QuotientGroup.mk' (Subgroup.center G))) →
      LinearIndependent ℝ v →
      Function.Bijective (nativeOrderedExponentialCoordinates (I := 𝓘(ℝ, F)) (G := Q) v) →
      (∀ x, nativeOrderedExponentialCoordinates (I := 𝓘(ℝ, F)) (G := Q) v x ∈
        Γ.map (QuotientGroup.mk' (Subgroup.center G)) ↔ ∀ i, ∃ n : ℤ, x i = (n : ℝ)) →
      ∃ w : Fin (m+nc) → E,
        (∀ i, nativeLieExponential (I := I) (G := G) (w i) ∈ Γ ∧
          w i ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ) ∧
        LinearIndependent ℝ w ∧
        Function.Bijective (nativeOrderedExponentialCoordinates (I := I) (G := G) w) ∧
        ∀ x, nativeOrderedExponentialCoordinates (I := I) (G := G) w x ∈ Γ ↔
          ∀ i, ∃ n : ℤ, x i = (n : ℝ) := by
  letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
  letI := nativeCenterQuotient_t2Space (I := I) (G := G)
  letI := nativeCenterQuotient_lieGroup (I := I) (G := G)
  letI := nativeCenterQuotient_simplyConnected (I := I) (G := G)
  let nc := Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G))
  dsimp only
  intro v hv hli hbij hlat
  obtain ⟨u, hu, hpair, hpairlat⟩ := native_center_coordinate_extension (I := I) Γ m v hv hbij hlat
  let c : Fin nc → E := fun i => (nativeCenterLatticeRealBasis (I := I) Γ i).val
  let e : (Fin (m+nc) → ℝ) ≃ (Fin m → ℝ) × (Fin nc → ℝ) := finiteCoordinateSplitEquiv m nc
  have hc : ∀ y, nativeOrderedExponentialCoordinates (I := I) (G := G) c y =
      (nativeCenterLatticeCoordinates (I := I) Γ y : G) := by
    intro y
    exact (native_center_lattice_coordinates_ordered_product (I := I) Γ y).symm
  have he : nativeOrderedExponentialCoordinates (I := I) (G := G) (Fin.append u c) =
      (fun x => nativeOrderedExponentialCoordinates (I := I) (G := G) u x.1 *
        (nativeCenterLatticeCoordinates (I := I) Γ x.2 : G)) ∘ e := by
    funext x
    rw [native_ordered_exponential_coordinates_split, hc]
    rfl
  refine ⟨Fin.append u c, ?_,
    native_center_lattice_lift_append_independent Γ v hli u (fun i => (hu i).2.2), ?_, ?_⟩
  · intro i
    cases i using Fin.addCases with
    | left i => simpa only [Fin.append_left] using ⟨(hu i).1, (hu i).2.1⟩
    | right i =>
      simpa only [Fin.append_right] using
        ⟨native_center_lattice_basis_exponential_mem Γ i,
          native_center_lattice_basis_mem_original_rational_span Γ i⟩
  · rw [he]
    exact hpair.comp e.bijective
  · intro x
    rw [he]
    change (nativeOrderedExponentialCoordinates (I := I) (G := G) u (e x).1 *
      (nativeCenterLatticeCoordinates (I := I) Γ (e x).2 : G) ∈ Γ) ↔ _
    rw [hpairlat (e x)]
    exact (finite_coordinate_split_predicate_iff m nc (fun r : ℝ => ∃ n : ℤ, r = (n : ℝ)) x).symm

end Hindman168
