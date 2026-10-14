import Hindman168.NativeCenterQuotientRationalKernel
import Hindman168.NativeCenterQuotientDimension
import Hindman168.NativeCenterQuotientLattice

/-! Full rational-dimension induction through the actual original center
quotients. First use the identity model for the quotient induction;
then apply one genuine center-quotient step to an arbitrary ORIGINAL
model with corners. The original group and specified lattice are kept. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u v

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLattice_identityModel_rationalLogSpan_finrank
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
    [FiniteDimensional ℝ E]
    {G : Type v} [TopologicalSpace G] [ChartedSpace E G] [Group G]
    [LieGroup 𝓘(ℝ, E) ∞ G] [BoundarylessManifold 𝓘(ℝ, E) G] [T2Space G]
    [Group.IsNilpotent G] [ConnectedSpace G] [SimplyConnectedSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    Module.finrank ℚ (nativeSubgroupRationalLogSpan (E := E) (I := 𝓘(ℝ, E)) Γ) =
      Module.finrank ℝ E := by
  have hmain : ∀ n : ℕ,
      ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [Module ℚ F]
        [FiniteDimensional ℝ F],
      ∀ {Q : Type v} [TopologicalSpace Q] [ChartedSpace F Q] [Group Q]
        [LieGroup 𝓘(ℝ, F) ∞ Q] [BoundarylessManifold 𝓘(ℝ, F) Q] [T2Space Q]
        [Group.IsNilpotent Q] [ConnectedSpace Q] [SimplyConnectedSpace Q],
      ∀ (Δ : Subgroup Q) [DiscreteTopology Δ] [CompactSpace (Q ⧸ Δ)],
        Module.finrank ℝ F = n →
          Module.finrank ℚ (nativeSubgroupRationalLogSpan (E := F) (I := 𝓘(ℝ, F)) Δ) =
            Module.finrank ℝ F := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro F hAdd hNorm hComplete hRat hFinite Q hTop hChart hGroup hLie hBoundary
        hT2 hNil hConnected hSimply Δ hDisc hCompact hdim
      rcases subsingleton_or_nontrivial Q with htriv | hnontriv
      · letI := htriv
        letI : Subsingleton F := ⟨fun x y =>
          nativeLieExponential_injective (E := F) (I := 𝓘(ℝ, F)) (G := Q)
            (Subsingleton.elim _ _)⟩
        simp only [Module.finrank_zero_of_subsingleton]
      · letI := hnontriv
        let C := nativeLieCenterModel (I := 𝓘(ℝ, F)) (G := Q)
        have hlt : Module.finrank ℝ (F ⧸ C) < n := by
          simpa only [hdim] using
            nativeCenterQuotientModel_finrank_lt (E := F) (I := 𝓘(ℝ, F)) (G := Q)
        apply nativeLattice_rationalLogSpan_finrank_center_step (E := F) (I := 𝓘(ℝ, F)) Δ
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

 theorem nativeLattice_rationalLogSpan_finrank (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    Module.finrank ℚ (nativeSubgroupRationalLogSpan (E := E) (I := I) Γ) =
      Module.finrank ℝ E := by
  apply nativeLattice_rationalLogSpan_finrank_center_step (E := E) (I := I) Γ
  letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
  letI := nativeCenterQuotient_isManifold (I := I) (G := G)
  letI := nativeCenterQuotient_t2Space (I := I) (G := G)
  letI := nativeCenterQuotient_lieGroup (I := I) (G := G)
  letI := nativeCenterQuotient_simplyConnected (I := I) (G := G)
  letI := nativeLattice_center_quotient_image_discrete (E := E) (I := I) Γ
  letI := nativeLattice_center_quotient_image_cocompact Γ
  exact nativeLattice_identityModel_rationalLogSpan_finrank _

end Hindman168
