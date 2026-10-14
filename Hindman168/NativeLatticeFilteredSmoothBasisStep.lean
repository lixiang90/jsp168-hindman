import Hindman168.NativeLatticeFilteredSmoothBasisExist
import Hindman168.NativeCentralSubspaceFlagGeneratorLift
import Hindman168.NativeCentralSubspaceOrderedSmoothExtension
import Hindman168.NativeCentralSubspaceLatticeBasisSpan
import Hindman168.ProjectionAppendLayerSpan

namespace Hindman168
open Submodule Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three
attribute [local instance] nativeCentralSubspaceSubgroup_normal

theorem native_lattice_filtered_smooth_basis_terminal_step (Γ : Subgroup G) [DiscreteTopology Γ]
    (j : ℕ) (hnext : nativeLieLowerCentralModel (I := I) (G := G) (j+1) = ⊥)
    (hV : nativeLieLowerCentralModel (I := I) (G := G) j ≤ nativeLieCenterModel (I := I) (G := G))
    (hrat : nativeLatticeRationalSubspace (E := E) (I := I) Γ
      (nativeLieLowerCentralModel (I := I) (G := G) j)) :
    let V := nativeLieLowerCentralModel (I := I) (G := G) j
    letI : IsClosed (V : Set E) := V.closed_of_finiteDimensional
    letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
    letI := nativeCentralSubspaceQuotient_t2Space (I := I) V hV
    letI := nativeCentralSubspaceQuotient_lieGroup (I := I) V hV
    letI := nativeCentralSubspaceQuotient_simplyConnected (I := I) V hV
    NativeLatticeFilteredSmoothBasisExist (E := E ⧸ V) (I := 𝓘(ℝ, E ⧸ V))
      (Γ.map (QuotientGroup.mk' (nativeCentralSubspaceSubgroup (I := I) V hV))) →
        NativeLatticeFilteredSmoothBasisExist (E := E) (I := I) Γ := by
  let V := nativeLieLowerCentralModel (I := I) (G := G) j
  letI : IsClosed (V : Set E) := V.closed_of_finiteDimensional
  letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
  letI := nativeCentralSubspaceQuotient_t2Space (I := I) V hV
  letI := nativeCentralSubspaceQuotient_lieGroup (I := I) V hV
  letI := nativeCentralSubspaceQuotient_simplyConnected (I := I) V hV
  let Q := G ⧸ nativeCentralSubspaceSubgroup (I := I) V hV
  let J := 𝓘(ℝ, E ⧸ V)
  let π := finiteRealQuotientProjection V
  have hprior : ∀ k ≤ j, V ≤ nativeLieLowerCentralModel (I := I) (G := G) k :=
    fun _ hk => nativeLieLowerCentralModel_antitone (I := I) (G := G) hk
  dsimp only
  intro h
  obtain ⟨m, hm, v, hv, hli, hbij, hlat, hinv, t, ht⟩ := h
  obtain ⟨u, hu⟩ := native_central_subspace_lattice_flag_generator_lifts (I := I) Γ V hV j hprior
    v (fun i => (hv i).1)
  obtain ⟨hwΓ, hwli, hwbij, hwlat, hwinv⟩ :=
    native_central_subspace_ordered_smooth_extension (I := I) Γ V hV hrat m v u
      (fun i => (hu i).1) (fun i => (hu i).2.2.1) hli hbij hlat hinv
  let nc := Module.finrank ℝ V
  let c : Fin nc → E := fun i => (nativeCentralSubspaceLatticeRealBasis (I := I) Γ V hV hrat i).val
  let w := Fin.append u c
  have hdim : m+nc = Module.finrank ℝ E := by
    rw [hm]
    exact V.finrank_quotient_add_finrank
  have hc : span ℝ (range c) = V :=
    native_central_subspace_lattice_columns_real_span (I := I) Γ V hV hrat
  have hker : π.toLinearMap.ker = V := Submodule.ker_mkQ V
  refine ⟨m+nc, hdim, w, hwΓ, hwli, hwbij, hwlat, hwinv,
    fun k => if k ≤ j then t k else m+nc, ?_⟩
  intro k
  by_cases hk : k ≤ j
  · simp only [if_pos hk]
    have htbound : t k ≤ m+nc := (ht k).1.trans (Nat.le_add_right m nc)
    have hmem : ∀ i, w i ∈ nativeLieLowerCentralModel (I := I) (G := G) k ↔ t k ≤ i.val := by
      intro i
      cases i using Fin.addCases with
      | left i =>
        simpa only [w, Fin.append_left, Fin.val_castAdd] using
          ((hu i).2.2.2 k hk).trans ((ht k).2.1 i)
      | right i =>
        have hcP : c i ∈ nativeLieLowerCentralModel (I := I) (G := G) k :=
          hprior k hk (nativeCentralSubspaceLatticeRealBasis (I := I) Γ V hV hrat i).property
        have hb : t k ≤ m+i.val := (ht k).1.trans (Nat.le_add_right m i.val)
        simpa only [w, Fin.append_right, Fin.val_natAdd] using
          (show c i ∈ nativeLieLowerCentralModel (I := I) (G := G) k ↔ t k ≤ m+i.val from
            ⟨fun _ => hb, fun _ => hcP⟩)
    refine ⟨htbound, hmem, ?_⟩
    have hspanQ : span ℝ (v '' {i | v i ∈ nativeLieLowerCentralModel (I := J) (G := Q) k}) =
        nativeLieLowerCentralModel (I := J) (G := Q) k := by
      have he : {i | v i ∈ nativeLieLowerCentralModel (I := J) (G := Q) k} =
          {i | t k ≤ i.val} := Set.ext (fun i => (ht k).2.1 i)
      rw [he]
      exact (ht k).2.2
    have hmap : (nativeLieLowerCentralModel (I := I) (G := G) k).map π.toLinearMap =
        nativeLieLowerCentralModel (I := J) (G := Q) k :=
      nativeCentralSubspaceQuotient_lie_layer_image (I := I) V hV k
    have hkerP : π.toLinearMap.ker ≤ nativeLieLowerCentralModel (I := I) (G := G) k := by
      rw [hker]
      exact hprior k hk
    have hs := projection_append_layer_span π.toLinearMap u v c
      (fun i => (hu i).2.2.1) (hc.trans hker.symm)
      (nativeLieLowerCentralModel (I := I) (G := G) k)
      (nativeLieLowerCentralModel (I := J) (G := Q) k)
      hkerP hmap (fun i => (hu i).2.2.2 k hk) hspanQ
    have he : {i | w i ∈ nativeLieLowerCentralModel (I := I) (G := G) k} =
        {i | t k ≤ i.val} := Set.ext hmem
    change span ℝ (w '' {i | t k ≤ i.val}) = _
    rw [← he]
    exact hs
  · simp only [if_neg hk]
    have hbot : nativeLieLowerCentralModel (I := I) (G := G) k = ⊥ := by
      apply le_antisymm
      · exact hnext ▸ nativeLieLowerCentralModel_antitone (I := I) (G := G) (by omega : j+1 ≤ k)
      · exact bot_le
    refine ⟨le_rfl, ?_, ?_⟩
    · intro i
      rw [hbot, Submodule.mem_bot]
      constructor
      · intro hz
        exact False.elim (hwli.ne_zero i hz)
      · intro hi
        exact False.elim (Nat.not_le_of_gt i.isLt hi)
    · have he : {i : Fin (m+nc) | m+nc ≤ i.val} = ∅ := by
        ext i
        exact ⟨fun hi => False.elim (Nat.not_le_of_gt i.isLt hi), False.elim⟩
      rw [he, Set.image_empty, Submodule.span_empty, hbot]

end Hindman168
