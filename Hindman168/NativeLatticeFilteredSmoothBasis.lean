import Hindman168.NativeLatticeFilteredSmoothBasisStep
import Hindman168.NativeTerminalCentralSubspace
import Hindman168.NativeCentralSubspaceQuotientLattice

namespace Hindman168
open scoped Manifold ContDiff
universe u v

attribute [local instance] lieGroup_smooth_min_three
attribute [local instance] nativeCentralSubspaceSubgroup_normal

theorem native_lattice_identity_model_filtered_smooth_basis
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
    [FiniteDimensional ℝ E]
    {G : Type v} [TopologicalSpace G] [ChartedSpace E G] [Group G]
    [LieGroup 𝓘(ℝ, E) ∞ G] [BoundarylessManifold 𝓘(ℝ, E) G] [T2Space G]
    [Group.IsNilpotent G] [ConnectedSpace G] [SimplyConnectedSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    NativeLatticeFilteredSmoothBasisExist (E := E) (I := 𝓘(ℝ, E)) Γ := by
  have hmain : ∀ n : ℕ,
      ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [Module ℚ F]
        [FiniteDimensional ℝ F],
      ∀ {Q : Type v} [TopologicalSpace Q] [ChartedSpace F Q] [Group Q]
        [LieGroup 𝓘(ℝ, F) ∞ Q] [BoundarylessManifold 𝓘(ℝ, F) Q] [T2Space Q]
        [Group.IsNilpotent Q] [ConnectedSpace Q] [SimplyConnectedSpace Q],
      ∀ (Δ : Subgroup Q) [DiscreteTopology Δ] [CompactSpace (Q ⧸ Δ)],
        Module.finrank ℝ F = n → NativeLatticeFilteredSmoothBasisExist (E := F) (I := 𝓘(ℝ, F)) Δ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro F hAdd hNorm hComplete hRat hFinite Q hTop hChart hGroup hLie hBoundary
        hT2 hNil hConnected hSimply Δ hDisc hCompact hdim
      rcases subsingleton_or_nontrivial Q with htriv | hnontriv
      · letI := htriv
        exact native_lattice_filtered_smooth_basis_subsingleton (I := 𝓘(ℝ, F)) Δ
      · letI := hnontriv
        let e := (nativeLieExponentialDiffeomorph (E := F) (I := 𝓘(ℝ, F)) (G := Q)).toEquiv
        letI : Nontrivial F := e.symm.injective.nontrivial
        obtain ⟨j, _, hnext, hV, hrat, _, hlt⟩ :=
          nativeLattice_terminal_central_subspace_exists (I := 𝓘(ℝ, F)) Δ
        let V := nativeLieLowerCentralModel (I := 𝓘(ℝ, F)) (G := Q) j
        have hsmall : Module.finrank ℝ (F ⧸ V) < n := by
          simpa only [hdim] using hlt
        apply native_lattice_filtered_smooth_basis_terminal_step (I := 𝓘(ℝ, F)) Δ j hnext hV hrat
        letI : IsClosed (V : Set F) := V.closed_of_finiteDimensional
        letI := nativeCentralSubspaceQuotientChartedSpace (I := 𝓘(ℝ, F)) V hV
        letI := nativeCentralSubspaceQuotient_isManifold (I := 𝓘(ℝ, F)) V hV
        letI := nativeCentralSubspaceQuotient_t2Space (I := 𝓘(ℝ, F)) V hV
        letI := nativeCentralSubspaceQuotient_lieGroup (I := 𝓘(ℝ, F)) V hV
        letI := nativeCentralSubspaceQuotient_simplyConnected (I := 𝓘(ℝ, F)) V hV
        letI := nativeCentralSubspaceQuotient_lattice_image_discrete (I := 𝓘(ℝ, F)) Δ V hV hrat
        letI := nativeCentralSubspaceQuotient_lattice_image_cocompact (I := 𝓘(ℝ, F)) Δ V hV
        exact ih (Module.finrank ℝ (F ⧸ V)) hsmall
          (F := F ⧸ V) (Q := Q ⧸ nativeCentralSubspaceSubgroup (I := 𝓘(ℝ, F)) V hV)
          (Δ.map (QuotientGroup.mk' (nativeCentralSubspaceSubgroup (I := 𝓘(ℝ, F)) V hV))) rfl
  exact hmain (Module.finrank ℝ E) Γ rfl

theorem native_lattice_filtered_smooth_basis
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
    [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
    [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    NativeLatticeFilteredSmoothBasisExist (E := E) (I := I) Γ := by
  rcases subsingleton_or_nontrivial G with htriv | hnontriv
  · letI := htriv
    exact native_lattice_filtered_smooth_basis_subsingleton (I := I) Γ
  · letI := hnontriv
    let e := (nativeLieExponentialDiffeomorph (E := E) (I := I) (G := G)).toEquiv
    letI : Nontrivial E := e.symm.injective.nontrivial
    obtain ⟨j, _, hnext, hV, hrat, _, _⟩ := nativeLattice_terminal_central_subspace_exists (I := I) Γ
    let V := nativeLieLowerCentralModel (I := I) (G := G) j
    apply native_lattice_filtered_smooth_basis_terminal_step (I := I) Γ j hnext hV hrat
    letI : IsClosed (V : Set E) := V.closed_of_finiteDimensional
    letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
    letI := nativeCentralSubspaceQuotient_isManifold (I := I) V hV
    letI := nativeCentralSubspaceQuotient_t2Space (I := I) V hV
    letI := nativeCentralSubspaceQuotient_lieGroup (I := I) V hV
    letI := nativeCentralSubspaceQuotient_simplyConnected (I := I) V hV
    letI := nativeCentralSubspaceQuotient_lattice_image_discrete (I := I) Γ V hV hrat
    letI := nativeCentralSubspaceQuotient_lattice_image_cocompact (I := I) Γ V hV
    exact native_lattice_identity_model_filtered_smooth_basis
      (Γ.map (QuotientGroup.mk' (nativeCentralSubspaceSubgroup (I := I) V hV)))

end Hindman168
