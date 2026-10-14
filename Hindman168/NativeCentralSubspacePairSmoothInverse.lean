import Hindman168.NativeCentralSubspaceCoordinateRecovery
import Hindman168.NativeOrderedExponentialSmooth
import Hindman168.NativeCentralSubspaceQuotientSmoothProjection
import Hindman168.NativeCentralSubspaceOrderedProjection

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three
attribute [local instance] nativeCentralSubspaceSubgroup_normal

theorem native_central_subspace_pair_smooth_inverse (Γ : Subgroup G)
    [DiscreteTopology Γ] (V : Submodule ℝ E) [IsClosed (V : Set E)]
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G))
    (hrat : nativeLatticeRationalSubspace (E := E) (I := I) Γ V) (m : ℕ) :
    letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
    letI := nativeCentralSubspaceQuotient_t2Space (I := I) V hV
    letI := nativeCentralSubspaceQuotient_lieGroup (I := I) V hV
    let F := E ⧸ V
    let Q := G ⧸ (nativeCentralSubspaceSubgroup (I := I) V hV)
    let C := Fin (Module.finrank ℝ (V)) → ℝ
    ∀ (v : Fin m → F) (u : Fin m → E),
      (∀ i, finiteRealQuotientProjection V (u i) = v i) →
      ∀ rQ : Q → (Fin m → ℝ),
      Function.RightInverse rQ (nativeOrderedExponentialCoordinates (I := 𝓘(ℝ, F)) (G := Q) v) →
      ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, Fin m → ℝ) ∞ rQ →
      Function.Bijective (fun x : (Fin m → ℝ) × C =>
        nativeOrderedExponentialCoordinates (I := I) (G := G) u x.1 *
          (nativeCentralSubspaceLatticeCoordinates (I := I) Γ V hV hrat x.2 : G)) →
      ∃ r : G → (Fin m → ℝ) × C,
        Function.LeftInverse r (fun x =>
          nativeOrderedExponentialCoordinates (I := I) (G := G) u x.1 *
            (nativeCentralSubspaceLatticeCoordinates (I := I) Γ V hV hrat x.2 : G)) ∧
        Function.RightInverse r (fun x =>
          nativeOrderedExponentialCoordinates (I := I) (G := G) u x.1 *
            (nativeCentralSubspaceLatticeCoordinates (I := I) Γ V hV hrat x.2 : G)) ∧
        ContMDiff I 𝓘(ℝ, (Fin m → ℝ) × C) ∞ r := by
  letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
  letI := nativeCentralSubspaceQuotient_t2Space (I := I) V hV
  letI := nativeCentralSubspaceQuotient_lieGroup (I := I) V hV
  dsimp only
  intro v u hu rQ hrQ hsQ hbij
  let q : G →* G ⧸ (nativeCentralSubspaceSubgroup (I := I) V hV) := QuotientGroup.mk' ((nativeCentralSubspaceSubgroup (I := I) V hV))
  let a : G → (Fin m → ℝ) := fun g => rQ (q g)
  let s : (Fin m → ℝ) → G := nativeOrderedExponentialCoordinates (I := I) (G := G) u
  let z : G → G := fun g => (s (a g))⁻¹ * g
  let r := fun g : G => (a g, nativeCentralSubspaceCoordinateRecovery (I := I) Γ V hV hrat (z g))
  have ha : ContMDiff I 𝓘(ℝ, Fin m → ℝ) ∞ a :=
    hsQ.comp (nativeCentralSubspaceQuotient_projection_contMDiff (I := I) V hV)
  have hz : ContMDiff I I ∞ z :=
    ((native_ordered_exponential_coordinates_contMDiff (I := I) (G := G) u).comp ha).inv.mul
      contMDiff_id
  have hp : ∀ x, q (s x) =
      nativeOrderedExponentialCoordinates
        (I := 𝓘(ℝ, E ⧸ V))
        (G := G ⧸ (nativeCentralSubspaceSubgroup (I := I) V hV)) v x := by
    intro x
    have he := native_ordered_exponential_coordinates_central_subspace_projection (I := I) V hV u x
    rw [show (fun i => finiteRealQuotientProjection V (u i)) = v from funext hu] at he
    exact he
  have hzC : ∀ g, z g ∈ (nativeCentralSubspaceSubgroup (I := I) V hV) := by
    intro g
    apply (QuotientGroup.eq_one_iff (z g)).mp
    change q (z g) = 1
    change q ((s (a g))⁻¹ * g) = 1
    rw [map_mul, map_inv, hp, hrQ (q g), inv_mul_cancel]
  have hright : Function.RightInverse r (fun x => s x.1 *
      (nativeCentralSubspaceLatticeCoordinates (I := I) Γ V hV hrat x.2 : G)) := by
    intro g
    change s (a g) * (nativeCentralSubspaceLatticeCoordinates (I := I) Γ V hV hrat
      (nativeCentralSubspaceCoordinateRecovery (I := I) Γ V hV hrat (z g)) : G) = g
    rw [native_central_subspace_coordinate_recovery_right (I := I) Γ V hV hrat (z g) (hzC g)]
    exact mul_inv_cancel_left (s (a g)) g
  refine ⟨r, ?_, hright, ?_⟩
  · intro x
    apply hbij.1
    exact hright _
  · exact ha.prodMk_space ((native_central_subspace_coordinate_recovery_contMDiff (I := I) Γ V hV hrat).comp hz)

end Hindman168
