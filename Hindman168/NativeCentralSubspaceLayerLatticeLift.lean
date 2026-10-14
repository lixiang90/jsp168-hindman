import Hindman168.NativeCentralSubspaceLowerCentralImage
import Hindman168.NativeCentralLayerKernel
import Hindman168.KernelContainedLayerLatticeLift

/-! Relative lattice lifts for a genuine central quotient. The specified
central subspace must lie in the layer; the actual quotient kernel then
satisfies the containment required by intersection-image lifting. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three
attribute [local instance] nativeCentralSubspaceSubgroup_normal

theorem nativeCentralSubspaceQuotient_lattice_layer_image (Γ : Subgroup G)
    (V : Submodule ℝ E) (hV : V ≤ nativeLieCenterModel (I := I) (G := G))
    (j : ℕ) (hj : V ≤ nativeLieLowerCentralModel (I := I) (G := G) j) :
    (Γ ⊓ (⊤ : Subgroup G).lowerCentralSeries j).map
      (QuotientGroup.mk' (nativeCentralSubspaceSubgroup (I := I) V hV)) =
      Γ.map (QuotientGroup.mk' (nativeCentralSubspaceSubgroup (I := I) V hV)) ⊓
        (⊤ : Subgroup (G ⧸ nativeCentralSubspaceSubgroup (I := I) V hV)).lowerCentralSeries j := by
  rw [lattice_layer_image_eq_of_kernel_le]
  · rw [nativeCentralSubspaceQuotient_group_layer_image (I := I) V hV]
  · rw [QuotientGroup.ker_mk']
    exact nativeCentralSubspaceSubgroup_le_group_layer V hV j hj

theorem nativeCentralSubspaceQuotient_lattice_layer_lift (Γ : Subgroup G)
    (V : Submodule ℝ E) (hV : V ≤ nativeLieCenterModel (I := I) (G := G))
    (j : ℕ) (hj : V ≤ nativeLieLowerCentralModel (I := I) (G := G) j)
    (x : G ⧸ nativeCentralSubspaceSubgroup (I := I) V hV)
    (hxΓ : x ∈ Γ.map (QuotientGroup.mk' (nativeCentralSubspaceSubgroup (I := I) V hV)))
    (hxj : x ∈ (⊤ : Subgroup (G ⧸ nativeCentralSubspaceSubgroup (I := I) V hV)).lowerCentralSeries j) :
    ∃ g : G, g ∈ Γ ∧ g ∈ (⊤ : Subgroup G).lowerCentralSeries j ∧ QuotientGroup.mk g = x := by
  have hx : x ∈ (Γ ⊓ (⊤ : Subgroup G).lowerCentralSeries j).map
      (QuotientGroup.mk' (nativeCentralSubspaceSubgroup (I := I) V hV)) := by
    rw [nativeCentralSubspaceQuotient_lattice_layer_image Γ V hV j hj]
    exact ⟨hxΓ, hxj⟩
  obtain ⟨g, hg, he⟩ := hx
  exact ⟨g, hg.1, hg.2, he⟩

theorem nativeCentralSubspaceQuotient_lie_lattice_layer_lift (Γ : Subgroup G)
    (V : Submodule ℝ E)
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G))
    (j : ℕ) (hj : V ≤ nativeLieLowerCentralModel (I := I) (G := G) j) :
    letI : IsClosed (V : Set E) := V.closed_of_finiteDimensional
    letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
    letI := nativeCentralSubspaceQuotient_t2Space (I := I) V hV
    letI := nativeCentralSubspaceQuotient_lieGroup (I := I) V hV
    letI := nativeCentralSubspaceQuotient_simplyConnected (I := I) V hV
    ∀ y : E ⧸ V,
      nativeLieExponential (I := 𝓘(ℝ, E ⧸ V))
        (G := G ⧸ nativeCentralSubspaceSubgroup (I := I) V hV) y ∈
          Γ.map (QuotientGroup.mk' (nativeCentralSubspaceSubgroup (I := I) V hV)) →
      y ∈ nativeLieLowerCentralModel (I := 𝓘(ℝ, E ⧸ V))
        (G := G ⧸ nativeCentralSubspaceSubgroup (I := I) V hV) j →
      ∃ v : E, v ∈ nativeLieLowerCentralModel (I := I) (G := G) j ∧
        nativeLieExponential (I := I) (G := G) v ∈ Γ ∧ V.mkQ v = y := by
  letI : IsClosed (V : Set E) := V.closed_of_finiteDimensional
  letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
  letI := nativeCentralSubspaceQuotient_t2Space (I := I) V hV
  letI := nativeCentralSubspaceQuotient_lieGroup (I := I) V hV
  letI := nativeCentralSubspaceQuotient_simplyConnected (I := I) V hV
  let Q := G ⧸ nativeCentralSubspaceSubgroup (I := I) V hV
  let J := 𝓘(ℝ, E ⧸ V)
  intro y hyΓ hyj
  have hxj : nativeLieExponential (I := J) (G := Q) y ∈
      (⊤ : Subgroup Q).lowerCentralSeries j := by
    rw [nativeGroupLowerCentralSeries_eq_exponential (E := E ⧸ V) (I := J)]
    exact ⟨y, hyj, rfl⟩
  obtain ⟨g, hgΓ, hgj, he⟩ := nativeCentralSubspaceQuotient_lattice_layer_lift
    Γ V hV j hj _ hyΓ hxj
  rw [nativeGroupLowerCentralSeries_eq_exponential (E := E) (I := I)] at hgj
  obtain ⟨v, hv, rfl⟩ := hgj
  have heq := nativeCentralSubspaceQuotient_nativeExponential_projection (I := I) V hV v
  exact ⟨v, hv, hgΓ, (nativeLieExponential_injective (I := J) (G := Q)) (heq.symm.trans he)⟩

end Hindman168
