import Hindman168.NativeCenterOrderedCoordinateExtension
import Hindman168.NativeCenterQuotientDimension
import Hindman168.NativeCenterQuotientLattice

namespace Hindman168
open scoped Manifold ContDiff
universe u v

attribute [local instance] lieGroup_smooth_min_three

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

def NativeLatticeOrderedCoordinatesExist (Γ : Subgroup G) : Prop :=
  ∃ m : ℕ, m = Module.finrank ℝ E ∧ ∃ w : Fin m → E,
    (∀ i, nativeLieExponential (I := I) (G := G) (w i) ∈ Γ ∧
      w i ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ) ∧
    Function.Bijective (nativeOrderedExponentialCoordinates (I := I) (G := G) w) ∧
    ∀ x, nativeOrderedExponentialCoordinates (I := I) (G := G) w x ∈ Γ ↔
      ∀ i, ∃ n : ℤ, x i = (n : ℝ)

theorem native_lattice_ordered_coordinates_subsingleton (Γ : Subgroup G) [Subsingleton G] :
    NativeLatticeOrderedCoordinatesExist (E := E) (I := I) Γ := by
  letI : Subsingleton E := ⟨fun x y => nativeLieExponential_injective (I := I) (G := G)
    (Subsingleton.elim _ _)⟩
  refine ⟨0, (Module.finrank_zero_of_subsingleton (R := ℝ) (M := E)).symm,
    Fin.elim0, (fun i => Fin.elim0 i), ?_, ?_⟩
  · exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun g => ⟨Fin.elim0, Subsingleton.elim _ _⟩⟩
  · intro x
    constructor
    · intro _ i
      exact Fin.elim0 i
    · intro _
      simpa only [nativeOrderedExponentialCoordinates, List.ofFn_zero, List.prod_nil] using Γ.one_mem

theorem native_lattice_ordered_coordinates_center_step (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
    letI := nativeCenterQuotient_t2Space (I := I) (G := G)
    letI := nativeCenterQuotient_lieGroup (I := I) (G := G)
    letI := nativeCenterQuotient_simplyConnected (I := I) (G := G)
    NativeLatticeOrderedCoordinatesExist
      (E := E ⧸ nativeLieCenterModel (I := I) (G := G))
      (I := 𝓘(ℝ, E ⧸ nativeLieCenterModel (I := I) (G := G)))
      (Γ.map (QuotientGroup.mk' (Subgroup.center G))) →
        NativeLatticeOrderedCoordinatesExist (E := E) (I := I) Γ := by
  letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
  letI := nativeCenterQuotient_t2Space (I := I) (G := G)
  letI := nativeCenterQuotient_lieGroup (I := I) (G := G)
  letI := nativeCenterQuotient_simplyConnected (I := I) (G := G)
  intro h
  obtain ⟨m, hm, v, hv, hbij, hlat⟩ := h
  obtain ⟨w, hw, hwb, hwl⟩ := native_center_ordered_coordinate_extension (I := I) Γ m v
    (fun i => (hv i).1) hbij hlat
  refine ⟨m+Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G)), ?_, w, hw, hwb, hwl⟩
  rw [hm]
  exact (nativeLieCenterModel (I := I) (G := G)).finrank_quotient_add_finrank

end Hindman168

namespace Hindman168
open scoped Manifold ContDiff
universe u v

theorem native_lattice_identity_model_ordered_coordinates
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
    [FiniteDimensional ℝ E]
    {G : Type v} [TopologicalSpace G] [ChartedSpace E G] [Group G]
    [LieGroup 𝓘(ℝ, E) ∞ G] [BoundarylessManifold 𝓘(ℝ, E) G] [T2Space G]
    [Group.IsNilpotent G] [ConnectedSpace G] [SimplyConnectedSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    NativeLatticeOrderedCoordinatesExist (E := E) (I := 𝓘(ℝ, E)) Γ := by
  have hmain : ∀ n : ℕ,
      ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [Module ℚ F]
        [FiniteDimensional ℝ F],
      ∀ {Q : Type v} [TopologicalSpace Q] [ChartedSpace F Q] [Group Q]
        [LieGroup 𝓘(ℝ, F) ∞ Q] [BoundarylessManifold 𝓘(ℝ, F) Q] [T2Space Q]
        [Group.IsNilpotent Q] [ConnectedSpace Q] [SimplyConnectedSpace Q],
      ∀ (Δ : Subgroup Q) [DiscreteTopology Δ] [CompactSpace (Q ⧸ Δ)],
        Module.finrank ℝ F = n → NativeLatticeOrderedCoordinatesExist (E := F) (I := 𝓘(ℝ, F)) Δ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro F hAdd hNorm hComplete hRat hFinite Q hTop hChart hGroup hLie hBoundary
        hT2 hNil hConnected hSimply Δ hDisc hCompact hdim
      rcases subsingleton_or_nontrivial Q with htriv | hnontriv
      · letI := htriv
        exact native_lattice_ordered_coordinates_subsingleton (I := 𝓘(ℝ, F)) Δ
      · letI := hnontriv
        let C := nativeLieCenterModel (I := 𝓘(ℝ, F)) (G := Q)
        have hlt : Module.finrank ℝ (F ⧸ C) < n := by
          simpa only [hdim] using
            nativeCenterQuotientModel_finrank_lt (E := F) (I := 𝓘(ℝ, F)) (G := Q)
        apply native_lattice_ordered_coordinates_center_step (E := F) (I := 𝓘(ℝ, F)) Δ
        letI := nativeCenterQuotientChartedSpace (I := 𝓘(ℝ, F)) (G := Q)
        letI := nativeCenterQuotient_isManifold (I := 𝓘(ℝ, F)) (G := Q)
        letI := nativeCenterQuotient_t2Space (I := 𝓘(ℝ, F)) (G := Q)
        letI := nativeCenterQuotient_lieGroup (I := 𝓘(ℝ, F)) (G := Q)
        letI := nativeCenterQuotient_simplyConnected (I := 𝓘(ℝ, F)) (G := Q)
        letI := nativeLattice_center_quotient_image_discrete (E := F) (I := 𝓘(ℝ, F)) Δ
        letI := nativeLattice_center_quotient_image_cocompact Δ
        exact ih (Module.finrank ℝ (F ⧸ C)) hlt
          (F := F ⧸ C) (Q := Q ⧸ Subgroup.center Q)
          (Δ.map (QuotientGroup.mk' (Subgroup.center Q))) rfl
  exact hmain (Module.finrank ℝ E) Γ rfl

theorem native_lattice_ordered_coordinates
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
    [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
    [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    NativeLatticeOrderedCoordinatesExist (E := E) (I := I) Γ := by
  apply native_lattice_ordered_coordinates_center_step (I := I) Γ
  letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
  letI := nativeCenterQuotient_isManifold (I := I) (G := G)
  letI := nativeCenterQuotient_t2Space (I := I) (G := G)
  letI := nativeCenterQuotient_lieGroup (I := I) (G := G)
  letI := nativeCenterQuotient_simplyConnected (I := I) (G := G)
  letI := nativeLattice_center_quotient_image_discrete (E := E) (I := I) Γ
  letI := nativeLattice_center_quotient_image_cocompact Γ
  exact native_lattice_identity_model_ordered_coordinates _

end Hindman168
