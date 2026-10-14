import Hindman168.NativeLieLayerLatticeCompact

namespace Hindman168
open Set Submodule
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

/-! Rational subspaces are spanned by vectors whose actual exponentials
belong to the original subgroup. This does not identify Log Gamma with
an additive lattice. Positive powers are cleared separately for each vector. -/

theorem nativeRationalSubspace_exponential_span (Γ : Subgroup G)
    (V : Submodule ℝ E)
    (hV : nativeLatticeRationalSubspace (E := E) (I := I) Γ V) :
    span ℝ {v : E | v ∈ V ∧ nativeLieExponential (I := I) (G := G) v ∈ Γ} = V := by
  apply le_antisymm
  · exact span_le.mpr (fun _ hv => hv.1)
  · conv_lhs => rw [← hV]
    apply span_le.mpr
    intro v hv
    obtain ⟨n, hn, hp⟩ :=
      (nativeSubgroupRationalLogSpan_mem_iff_positive_power (E := E) (I := I) Γ v).mp hv.2
    have hm : (n : ℝ) • v ∈
        span ℝ {w : E | w ∈ V ∧ nativeLieExponential (I := I) (G := G) w ∈ Γ} := by
      apply subset_span
      refine ⟨V.smul_mem (n : ℝ) hv.1, ?_⟩
      rw [nativeLieExponential_nat_smul]
      exact hp
    exact (Submodule.smul_mem_iff _ (show (n : ℝ) ≠ 0 by exact_mod_cast hn.ne')).mp hm

theorem nativeLieLowerCentralModel_exponential_span (Γ : Subgroup G)
    [CompactSpace (G ⧸ Γ)] (j : ℕ) :
    span ℝ {v : E | v ∈ nativeLieLowerCentralModel (I := I) (G := G) j ∧
      nativeLieExponential (I := I) (G := G) v ∈ Γ} =
        nativeLieLowerCentralModel (I := I) (G := G) j :=
  nativeRationalSubspace_exponential_span Γ _ (nativeLieLowerCentralModel_lattice_rational Γ j)

end Hindman168

