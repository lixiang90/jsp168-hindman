import Hindman168.IntegerLatticeFlagBasis
import Hindman168.NativeCenterLayerRealSpan
import Hindman168.NativeCenterLayerIntegerSplit

namespace Hindman168
open Set Submodule Module
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem native_center_layer_flag_integer_basis_exists (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    ∃ b : Basis (Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G)))) ℤ
        (nativeCenterLogLattice (I := I) Γ),
      ∀ j : ℕ, span ℤ (b '' {i | ((b i).val.val : E) ∈
        nativeLieLowerCentralModel (I := I) (G := G) j}) =
          nativeCenterLayerIntegerIntersection (I := I) Γ j := by
  letI := nativeCenterLogLattice_discrete (E := E) (I := I) Γ
  letI := nativeCenterLogLattice_isZLattice (E := E) (I := I) Γ
  let C := nativeLieCenterModel (I := I) (G := G)
  let L := nativeCenterLogLattice (I := I) Γ
  let s := Group.nilpotencyClass G
  let V : ℕ → Submodule ℝ C := fun j =>
    (nativeLieLowerCentralModel (I := I) (G := G) j).comap C.subtype
  have hV : Antitone V := fun i j hij =>
    Submodule.comap_mono (nativeLieLowerCentralModel_antitone (I := I) (G := G) hij)
  obtain ⟨b, hb, _⟩ := integer_lattice_flag_basis_exists L (s+1) (fun j => V j.val)
    (fun i j hij => hV hij) (fun j => native_center_layer_integer_real_span Γ j.val)
  refine ⟨b, ?_⟩
  intro j
  change span ℤ (b '' {i | (b i : C) ∈ V j}) = integerSubspaceIntersection L (V j)
  by_cases hj : j < s+1
  · exact hb ⟨j, hj⟩
  · have hs : s ≤ j := by omega
    have hbot : V s = ⊥ := by
      dsimp only [V, s]
      rw [nativeLieLowerCentralModel_nilpotencyClass_bot, Submodule.comap_bot]
      exact LinearMap.ker_eq_bot.mpr C.subtype_injective
    have he : V j = V s := by
      apply le_antisymm (hV hs)
      rw [hbot]
      exact bot_le
    rw [he]
    exact hb ⟨s, Nat.lt_succ_self s⟩

noncomputable def nativeCenterLayerIntegerBasis (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    Basis (Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G)))) ℤ
      (nativeCenterLogLattice (I := I) Γ) :=
  (native_center_layer_flag_integer_basis_exists (E := E) (I := I) Γ).choose

theorem native_center_layer_integer_basis_adapted (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (j : ℕ) :
    span ℤ (nativeCenterLayerIntegerBasis (I := I) Γ ''
      {i | (((nativeCenterLayerIntegerBasis (I := I) Γ i).val.val) : E) ∈
        nativeLieLowerCentralModel (I := I) (G := G) j}) =
          nativeCenterLayerIntegerIntersection (I := I) Γ j :=
  (native_center_layer_flag_integer_basis_exists (E := E) (I := I) Γ).choose_spec j

noncomputable def nativeCenterLayerRealBasis (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    Basis (Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G)))) ℝ
      (nativeLieCenterModel (I := I) (G := G)) := by
  letI := nativeCenterLogLattice_discrete (E := E) (I := I) Γ
  letI := nativeCenterLogLattice_isZLattice (E := E) (I := I) Γ
  exact (nativeCenterLayerIntegerBasis (I := I) Γ).ofZLatticeBasis ℝ _

theorem native_center_layer_real_basis_apply (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (i : Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G)))) :
    nativeCenterLayerRealBasis (I := I) Γ i =
      (nativeCenterLayerIntegerBasis (I := I) Γ i).val := by
  letI := nativeCenterLogLattice_discrete (E := E) (I := I) Γ
  letI := nativeCenterLogLattice_isZLattice (E := E) (I := I) Γ
  exact Basis.ofZLatticeBasis_apply ℝ _ _ i

theorem native_center_layer_real_basis_adapted (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (j : ℕ) :
    span ℝ (nativeCenterLayerRealBasis (I := I) Γ ''
      {i | (nativeCenterLayerRealBasis (I := I) Γ i).val ∈
        nativeLieLowerCentralModel (I := I) (G := G) j}) =
      (nativeLieLowerCentralModel (I := I) (G := G) j).comap
        (nativeLieCenterModel (I := I) (G := G)).subtype := by
  letI := nativeCenterLogLattice_discrete (E := E) (I := I) Γ
  letI := nativeCenterLogLattice_isZLattice (E := E) (I := I) Γ
  let C := nativeLieCenterModel (I := I) (G := G)
  let L := nativeCenterLogLattice (I := I) Γ
  let V := (nativeLieLowerCentralModel (I := I) (G := G) j).comap C.subtype
  let b := nativeCenterLayerIntegerBasis (I := I) Γ
  change span ℝ (b.ofZLatticeBasis ℝ L '' {i | b.ofZLatticeBasis ℝ L i ∈ V}) = V
  exact integer_lattice_basis_layer_real_span L b V
    (native_center_layer_integer_basis_adapted Γ j) (native_center_layer_integer_real_span Γ j)

end Hindman168
