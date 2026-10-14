import Hindman168.NativeCenterCoordinateRecovery
import Hindman168.NativeOrderedExponentialSmooth
import Hindman168.NativeCenterQuotientSmoothProjection

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem native_center_pair_smooth_inverse (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (m : ℕ) :
    letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
    letI := nativeCenterQuotient_t2Space (I := I) (G := G)
    letI := nativeCenterQuotient_lieGroup (I := I) (G := G)
    let F := E ⧸ nativeLieCenterModel (I := I) (G := G)
    let Q := G ⧸ Subgroup.center G
    let C := Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G))) → ℝ
    ∀ (v : Fin m → F) (u : Fin m → E),
      (∀ i, nativeCenterQuotientProjection (I := I) (G := G) (u i) = v i) →
      ∀ rQ : Q → (Fin m → ℝ),
      Function.RightInverse rQ (nativeOrderedExponentialCoordinates (I := 𝓘(ℝ, F)) (G := Q) v) →
      ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, Fin m → ℝ) ∞ rQ →
      Function.Bijective (fun x : (Fin m → ℝ) × C =>
        nativeOrderedExponentialCoordinates (I := I) (G := G) u x.1 *
          (nativeCenterLatticeCoordinates (I := I) Γ x.2 : G)) →
      ∃ r : G → (Fin m → ℝ) × C,
        Function.LeftInverse r (fun x =>
          nativeOrderedExponentialCoordinates (I := I) (G := G) u x.1 *
            (nativeCenterLatticeCoordinates (I := I) Γ x.2 : G)) ∧
        Function.RightInverse r (fun x =>
          nativeOrderedExponentialCoordinates (I := I) (G := G) u x.1 *
            (nativeCenterLatticeCoordinates (I := I) Γ x.2 : G)) ∧
        ContMDiff I 𝓘(ℝ, (Fin m → ℝ) × C) ∞ r := by
  letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
  letI := nativeCenterQuotient_t2Space (I := I) (G := G)
  letI := nativeCenterQuotient_lieGroup (I := I) (G := G)
  dsimp only
  intro v u hu rQ hrQ hsQ hbij
  let q : G →* G ⧸ Subgroup.center G := QuotientGroup.mk' (Subgroup.center G)
  let a : G → (Fin m → ℝ) := fun g => rQ (q g)
  let s : (Fin m → ℝ) → G := nativeOrderedExponentialCoordinates (I := I) (G := G) u
  let z : G → G := fun g => (s (a g))⁻¹ * g
  let r := fun g : G => (a g, nativeCenterCoordinateRecovery (I := I) Γ (z g))
  have ha : ContMDiff I 𝓘(ℝ, Fin m → ℝ) ∞ a :=
    hsQ.comp (nativeCenterQuotient_projection_contMDiff (I := I) (G := G))
  have hz : ContMDiff I I ∞ z :=
    ((native_ordered_exponential_coordinates_contMDiff (I := I) (G := G) u).comp ha).inv.mul
      contMDiff_id
  have hp : ∀ x, q (s x) =
      nativeOrderedExponentialCoordinates
        (I := 𝓘(ℝ, E ⧸ nativeLieCenterModel (I := I) (G := G)))
        (G := G ⧸ Subgroup.center G) v x := by
    intro x
    have he := native_ordered_exponential_coordinates_center_projection (I := I) (G := G) u x
    rw [show (fun i => nativeCenterQuotientProjection (I := I) (G := G) (u i)) = v from funext hu] at he
    exact he
  have hzC : ∀ g, z g ∈ Subgroup.center G := by
    intro g
    apply (QuotientGroup.eq_one_iff (z g)).mp
    change q (z g) = 1
    change q ((s (a g))⁻¹ * g) = 1
    rw [map_mul, map_inv, hp, hrQ (q g), inv_mul_cancel]
  have hright : Function.RightInverse r (fun x => s x.1 *
      (nativeCenterLatticeCoordinates (I := I) Γ x.2 : G)) := by
    intro g
    change s (a g) * (nativeCenterLatticeCoordinates (I := I) Γ
      (nativeCenterCoordinateRecovery (I := I) Γ (z g)) : G) = g
    rw [native_center_coordinate_recovery_right Γ (z g) (hzC g)]
    exact mul_inv_cancel_left (s (a g)) g
  refine ⟨r, ?_, hright, ?_⟩
  · intro x
    apply hbij.1
    exact hright _
  · exact ha.prodMk_space ((native_center_coordinate_recovery_contMDiff (I := I) Γ).comp hz)

end Hindman168
