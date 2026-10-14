import Hindman168.NativeCentralSubspacePairCoordinates
import Hindman168.NativeCentralSubspaceLatticeIndependent
import Hindman168.NativeCentralSubspaceOrderedCoordinates
import Hindman168.NativeCentralSubspacePairSmoothInverse
import Hindman168.NativeOrderedCoordinateAppend
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
attribute [local instance] nativeCentralSubspaceSubgroup_normal

theorem native_central_subspace_ordered_smooth_extension (Γ : Subgroup G) [DiscreteTopology Γ]
    (V : Submodule ℝ E) [IsClosed (V : Set E)]
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G))
    (hrat : nativeLatticeRationalSubspace (E := E) (I := I) Γ V) (m : ℕ) :
    letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
    letI := nativeCentralSubspaceQuotient_t2Space (I := I) V hV
    letI := nativeCentralSubspaceQuotient_lieGroup (I := I) V hV
    let F := E ⧸ V
    let Q := G ⧸ nativeCentralSubspaceSubgroup (I := I) V hV
    ∀ (v : Fin m → F) (u : Fin m → E),
      (∀ i, nativeLieExponential (I := I) (G := G) (u i) ∈ Γ) →
      (∀ i, finiteRealQuotientProjection V (u i) = v i) →
      LinearIndependent ℝ v →
      Function.Bijective (nativeOrderedExponentialCoordinates (I := 𝓘(ℝ, F)) (G := Q) v) →
      (∀ x, nativeOrderedExponentialCoordinates (I := 𝓘(ℝ, F)) (G := Q) v x ∈
        Γ.map (QuotientGroup.mk' (nativeCentralSubspaceSubgroup (I := I) V hV)) ↔
          ∀ i, ∃ n : ℤ, x i = (n : ℝ)) →
      NativeOrderedCoordinateSmoothInverse (I := 𝓘(ℝ, F)) (G := Q) v →
      let w := Fin.append u (fun i => (nativeCentralSubspaceLatticeRealBasis (I := I) Γ V hV hrat i).val)
      (∀ i, nativeLieExponential (I := I) (G := G) (w i) ∈ Γ ∧
        w i ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ) ∧
      LinearIndependent ℝ w ∧
      Function.Bijective (nativeOrderedExponentialCoordinates (I := I) (G := G) w) ∧
      (∀ x, nativeOrderedExponentialCoordinates (I := I) (G := G) w x ∈ Γ ↔
        ∀ i, ∃ n : ℤ, x i = (n : ℝ)) ∧
      NativeOrderedCoordinateSmoothInverse (I := I) (G := G) w := by
  letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
  letI := nativeCentralSubspaceQuotient_t2Space (I := I) V hV
  letI := nativeCentralSubspaceQuotient_lieGroup (I := I) V hV
  dsimp only
  intro v u huΓ hu hli hbij hlat hinv
  obtain ⟨hpair, hpairlat⟩ := native_central_subspace_pair_coordinates (I := I) Γ V hV hrat m
    v u huΓ hu hbij hlat
  obtain ⟨rQ, _, hrQ, hsQ⟩ := hinv
  obtain ⟨rp, hlp, hrp, hsp⟩ := native_central_subspace_pair_smooth_inverse (I := I) Γ V hV hrat m
    v u hu rQ hrQ hsQ hpair
  let nc := Module.finrank ℝ V
  let c : Fin nc → E := fun i => (nativeCentralSubspaceLatticeRealBasis (I := I) Γ V hV hrat i).val
  let e := finiteCoordinateSplitContinuousLinearEquiv m nc
  have hc : ∀ y, nativeOrderedExponentialCoordinates (I := I) (G := G) c y =
      (nativeCentralSubspaceLatticeCoordinates (I := I) Γ V hV hrat y : G) := by
    intro y
    exact (native_central_subspace_lattice_coordinates_ordered_product (I := I) Γ V hV hrat y).symm
  have he : nativeOrderedExponentialCoordinates (I := I) (G := G) (Fin.append u c) =
      (fun x => nativeOrderedExponentialCoordinates (I := I) (G := G) u x.1 *
        (nativeCentralSubspaceLatticeCoordinates (I := I) Γ V hV hrat x.2 : G)) ∘ e := by
    funext x
    rw [native_ordered_exponential_coordinates_split, hc]
    rfl
  refine ⟨?_, native_central_subspace_lattice_lift_append_independent (I := I) Γ V hV hrat v hli u hu,
    ?_, ?_, ?_⟩
  · intro i
    cases i using Fin.addCases with
    | left i =>
      have hr := nativeSubgroup_logarithm_mem_span (E := E) (I := I) Γ (huΓ i)
      have hr' : u i ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ := by
        simpa only [nativeLieGlobalLogarithm_exponential] using hr
      simpa only [Fin.append_left] using ⟨huΓ i, hr'⟩
    | right i =>
      simpa only [Fin.append_right] using
        ⟨native_central_subspace_lattice_basis_exponential_mem (I := I) Γ V hV hrat i,
          native_central_subspace_lattice_basis_mem_original_rational_span (I := I) Γ V hV hrat i⟩
  · rw [he]
    exact hpair.comp e.bijective
  · intro x
    rw [he]
    change (nativeOrderedExponentialCoordinates (I := I) (G := G) u (e x).1 *
      (nativeCentralSubspaceLatticeCoordinates (I := I) Γ V hV hrat (e x).2 : G) ∈ Γ) ↔ _
    rw [hpairlat (e x)]
    exact (finite_coordinate_split_predicate_iff m nc (fun r : ℝ => ∃ n : ℤ, r = (n : ℝ)) x).symm
  · refine ⟨fun g => e.symm (rp g), ?_, ?_, e.symm.contDiff.contMDiff.comp hsp⟩
    · intro x
      rw [he]
      change e.symm (rp (nativeOrderedExponentialCoordinates (I := I) (G := G) u (e x).1 *
        (nativeCentralSubspaceLatticeCoordinates (I := I) Γ V hV hrat (e x).2 : G))) = x
      rw [hlp, e.symm_apply_apply]
    · intro g
      rw [he]
      change nativeOrderedExponentialCoordinates (I := I) (G := G) u (e (e.symm (rp g))).1 *
        (nativeCentralSubspaceLatticeCoordinates (I := I) Γ V hV hrat (e (e.symm (rp g))).2 : G) = g
      rw [e.apply_symm_apply]
      exact hrp g

end Hindman168
