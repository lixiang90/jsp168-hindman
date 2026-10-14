import Hindman168.NativeCenterLatticeGeneratorLift
import Hindman168.NativeCenterOrderedCoordinates
import Hindman168.NativeOrderedExponentialCoordinates
import Hindman168.GroupKernelCoordinates

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [Module ℚ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem native_center_coordinate_extension (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (m : ℕ) :
    letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
    letI := nativeCenterQuotient_t2Space (I := I) (G := G)
    letI := nativeCenterQuotient_lieGroup (I := I) (G := G)
    letI := nativeCenterQuotient_simplyConnected (I := I) (G := G)
    let F := E ⧸ nativeLieCenterModel (I := I) (G := G)
    let Q := G ⧸ Subgroup.center G
    let C := Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G))) → ℝ
    ∀ v : Fin m → F,
      (∀ i, nativeLieExponential (I := 𝓘(ℝ, F)) (G := Q) (v i) ∈
        Γ.map (QuotientGroup.mk' (Subgroup.center G))) →
      Function.Bijective (nativeOrderedExponentialCoordinates (I := 𝓘(ℝ, F)) (G := Q) v) →
      (∀ x, nativeOrderedExponentialCoordinates (I := 𝓘(ℝ, F)) (G := Q) v x ∈
        Γ.map (QuotientGroup.mk' (Subgroup.center G)) ↔ ∀ i, ∃ n : ℤ, x i = (n : ℝ)) →
      ∃ u : Fin m → E,
        (∀ i, nativeLieExponential (I := I) (G := G) (u i) ∈ Γ ∧
          u i ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ ∧
          nativeCenterQuotientProjection (I := I) (G := G) (u i) = v i) ∧
        Function.Bijective (fun x : (Fin m → ℝ) × C =>
          nativeOrderedExponentialCoordinates (I := I) (G := G) u x.1 *
            (nativeCenterLatticeCoordinates (I := I) Γ x.2 : G)) ∧
        ∀ x : (Fin m → ℝ) × C,
          nativeOrderedExponentialCoordinates (I := I) (G := G) u x.1 *
              (nativeCenterLatticeCoordinates (I := I) Γ x.2 : G) ∈ Γ ↔
            (∀ i, ∃ n : ℤ, x.1 i = (n : ℝ)) ∧ (∀ i, ∃ n : ℤ, x.2 i = (n : ℝ)) := by
  letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
  letI := nativeCenterQuotient_t2Space (I := I) (G := G)
  letI := nativeCenterQuotient_lieGroup (I := I) (G := G)
  letI := nativeCenterQuotient_simplyConnected (I := I) (G := G)
  let F := E ⧸ nativeLieCenterModel (I := I) (G := G)
  let Q := G ⧸ Subgroup.center G
  let C := Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G))) → ℝ
  let q : G →* Q := QuotientGroup.mk' (Subgroup.center G)
  let c : C → G := fun x => (nativeCenterLatticeCoordinates (I := I) Γ x : G)
  dsimp only
  intro v hv hbij hlat
  obtain ⟨u, hu⟩ := native_center_lattice_generator_lifts (I := I) Γ v hv
  let s : (Fin m → ℝ) → G := nativeOrderedExponentialCoordinates (I := I) (G := G) u
  have hp : ∀ x, q (s x) = nativeOrderedExponentialCoordinates (I := 𝓘(ℝ, F)) (G := Q) v x := by
    intro x
    have h := native_ordered_exponential_coordinates_center_projection (I := I) (G := G) u x
    have he : (fun i => nativeCenterQuotientProjection (I := I) (G := G) (u i)) = v :=
      funext (fun i => (hu i).2.2)
    rw [he] at h
    change (QuotientGroup.mk' (Subgroup.center G)) (s x) = _
    rw [QuotientGroup.mk'_apply]
    exact h
  have hk : ∀ x, q (c x) = 1 := by
    intro x
    exact (QuotientGroup.eq_one_iff _).mpr (nativeCenterLatticeCoordinates (I := I) Γ x).property
  have hc : Function.Injective c := fun x y h =>
    (nativeCenterLatticeCoordinates (I := I) Γ).injective (Subtype.ext h)
  have hcover : ∀ g, q g = 1 → ∃ x, c x = g := by
    intro g hg
    have hgC : g ∈ Subgroup.center G := (QuotientGroup.eq_one_iff g).mp hg
    obtain ⟨x, hx⟩ := (nativeCenterLatticeCoordinates (I := I) Γ).surjective ⟨g, hgC⟩
    exact ⟨x, congrArg Subtype.val hx⟩
  have hs : Function.Bijective (fun x => q (s x)) := by
    have he : (fun x => q (s x)) = nativeOrderedExponentialCoordinates (I := 𝓘(ℝ, F)) (G := Q) v :=
      funext hp
    rw [he]
    exact hbij
  refine ⟨u, hu, group_kernel_coordinates_bijective q c s hc hk hcover hs, ?_⟩
  intro x
  apply group_kernel_coordinates_lattice_iff q Γ c s
    (fun y => ∀ i, ∃ n : ℤ, y i = (n : ℝ))
    (fun y => ∀ i, ∃ n : ℤ, y i = (n : ℝ)) hk
  · exact native_center_lattice_coordinates_mem_iff Γ
  · intro y
    rw [hp y]
    exact hlat y
  · intro y hy
    exact native_ordered_exponential_coordinates_integer_mem Γ u (fun i => (hu i).1) y hy

end Hindman168
