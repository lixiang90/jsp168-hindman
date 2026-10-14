import Hindman168.NativeCenterCoordinateExtension
import Hindman168.NativeCenterLatticeIndependent
import Hindman168.NativeOrderedCoordinateAppend
import Hindman168.NativeCenterPairSmoothInverse
import Hindman168.FiniteCoordinateSplitSmooth
import Hindman168.NativeOrderedSmoothInverse

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem native_center_ordered_smooth_basis_extension (Γ : Subgroup G)
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
      NativeOrderedCoordinateSmoothInverse (I := 𝓘(ℝ, F)) (G := Q) v →
      ∃ w : Fin (m+nc) → E,
        (∀ i, nativeLieExponential (I := I) (G := G) (w i) ∈ Γ ∧
          w i ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ) ∧
        LinearIndependent ℝ w ∧
        Function.Bijective (nativeOrderedExponentialCoordinates (I := I) (G := G) w) ∧
        (∀ x, nativeOrderedExponentialCoordinates (I := I) (G := G) w x ∈ Γ ↔
          ∀ i, ∃ n : ℤ, x i = (n : ℝ)) ∧
        NativeOrderedCoordinateSmoothInverse (I := I) (G := G) w := by
  letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
  letI := nativeCenterQuotient_t2Space (I := I) (G := G)
  letI := nativeCenterQuotient_lieGroup (I := I) (G := G)
  letI := nativeCenterQuotient_simplyConnected (I := I) (G := G)
  let nc := Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G))
  dsimp only
  intro v hv hli hbij hlat hinv
  obtain ⟨u, hu, hpair, hpairlat⟩ := native_center_coordinate_extension (I := I) Γ m v hv hbij hlat
  obtain ⟨rQ, _, hrQ, hsQ⟩ := hinv
  obtain ⟨rp, hlp, hrp, hsp⟩ := native_center_pair_smooth_inverse (I := I) Γ m v u
    (fun i => (hu i).2.2) rQ hrQ hsQ hpair
  let c : Fin nc → E := fun i => (nativeCenterLatticeRealBasis (I := I) Γ i).val
  let e := finiteCoordinateSplitContinuousLinearEquiv m nc
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
    native_center_lattice_lift_append_independent Γ v hli u (fun i => (hu i).2.2), ?_, ?_, ?_⟩
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
  · refine ⟨fun g => e.symm (rp g), ?_, ?_, e.symm.contDiff.contMDiff.comp hsp⟩
    · intro x
      rw [he]
      change e.symm (rp (nativeOrderedExponentialCoordinates (I := I) (G := G) u (e x).1 *
        (nativeCenterLatticeCoordinates (I := I) Γ (e x).2 : G))) = x
      rw [hlp, e.symm_apply_apply]
    · intro g
      rw [he]
      change nativeOrderedExponentialCoordinates (I := I) (G := G) u (e (e.symm (rp g))).1 *
        (nativeCenterLatticeCoordinates (I := I) Γ (e (e.symm (rp g))).2 : G) = g
      rw [e.apply_symm_apply]
      exact hrp g

end Hindman168
