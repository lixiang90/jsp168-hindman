import Hindman168.NativeCentralSubspaceLatticeCoordinates
import Hindman168.NativeCentralSubspaceOrderedProjection
import Hindman168.GroupKernelCoordinates

/-! The actual pair coordinate extension for any specified original lattice
lifts. Keeping the lifts as inputs allows later filtration-compatible choices. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three
attribute [local instance] nativeCentralSubspaceSubgroup_normal

theorem native_central_subspace_pair_coordinates (Γ : Subgroup G) [DiscreteTopology Γ]
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
      Function.Bijective (nativeOrderedExponentialCoordinates (I := 𝓘(ℝ, F)) (G := Q) v) →
      (∀ x, nativeOrderedExponentialCoordinates (I := 𝓘(ℝ, F)) (G := Q) v x ∈
        Γ.map (QuotientGroup.mk' (nativeCentralSubspaceSubgroup (I := I) V hV)) ↔
          ∀ i, ∃ n : ℤ, x i = (n : ℝ)) →
      Function.Bijective (fun x : (Fin m → ℝ) × (Fin (Module.finrank ℝ V) → ℝ) =>
        nativeOrderedExponentialCoordinates (I := I) (G := G) u x.1 *
          (nativeCentralSubspaceLatticeCoordinates (I := I) Γ V hV hrat x.2 : G)) ∧
      ∀ x : (Fin m → ℝ) × (Fin (Module.finrank ℝ V) → ℝ),
        nativeOrderedExponentialCoordinates (I := I) (G := G) u x.1 *
            (nativeCentralSubspaceLatticeCoordinates (I := I) Γ V hV hrat x.2 : G) ∈ Γ ↔
          (∀ i, ∃ n : ℤ, x.1 i = (n : ℝ)) ∧ (∀ i, ∃ n : ℤ, x.2 i = (n : ℝ)) := by
  letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
  letI := nativeCentralSubspaceQuotient_t2Space (I := I) V hV
  letI := nativeCentralSubspaceQuotient_lieGroup (I := I) V hV
  let F := E ⧸ V
  let Q := G ⧸ nativeCentralSubspaceSubgroup (I := I) V hV
  let q : G →* Q := QuotientGroup.mk' (nativeCentralSubspaceSubgroup (I := I) V hV)
  let c := fun x => (nativeCentralSubspaceLatticeCoordinates (I := I) Γ V hV hrat x : G)
  dsimp only
  intro v u huΓ hu hbij hlat
  let s := nativeOrderedExponentialCoordinates (I := I) (G := G) u
  have hp : ∀ x, q (s x) = nativeOrderedExponentialCoordinates (I := 𝓘(ℝ, F)) (G := Q) v x := by
    intro x
    have h := native_ordered_exponential_coordinates_central_subspace_projection (I := I) V hV u x
    rw [show (fun i => finiteRealQuotientProjection V (u i)) = v from funext hu] at h
    exact h
  have hk : ∀ x, q (c x) = 1 := fun x =>
    (QuotientGroup.eq_one_iff _).mpr (nativeCentralSubspaceLatticeCoordinates (I := I) Γ V hV hrat x).property
  have hc : Function.Injective c := fun x y h =>
    (nativeCentralSubspaceLatticeCoordinates (I := I) Γ V hV hrat).injective (Subtype.ext h)
  have hcover : ∀ g, q g = 1 → ∃ x, c x = g := by
    intro g hg
    have hgN := (QuotientGroup.eq_one_iff g).mp hg
    obtain ⟨x, hx⟩ := (nativeCentralSubspaceLatticeCoordinates (I := I) Γ V hV hrat).surjective ⟨g, hgN⟩
    exact ⟨x, congrArg Subtype.val hx⟩
  have hs : Function.Bijective (fun x => q (s x)) := by
    rw [show (fun x => q (s x)) =
      nativeOrderedExponentialCoordinates (I := 𝓘(ℝ, F)) (G := Q) v from funext hp]
    exact hbij
  refine ⟨group_kernel_coordinates_bijective q c s hc hk hcover hs, ?_⟩
  intro x
  apply group_kernel_coordinates_lattice_iff q Γ c s
    (fun y => ∀ i, ∃ n : ℤ, y i = (n : ℝ))
    (fun y => ∀ i, ∃ n : ℤ, y i = (n : ℝ)) hk
  · exact native_central_subspace_lattice_coordinates_mem_iff (I := I) Γ V hV hrat
  · intro y
    rw [hp y]
    exact hlat y
  · exact fun y hy => native_ordered_exponential_coordinates_integer_mem Γ u huΓ y hy

end Hindman168
