import Hindman168.NativeContinuousCharacterCommutator
import Mathlib.Topology.Instances.RealVectorSpace

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem native_continuous_character_horizontal_fibers (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (χ : G → ℝ)
    (hmul : ∀ g h, χ (g*h) = χ g + χ h) (g h : G)
    (heq : nativeFilteredHorizontalCoordinates (I := I) Γ g =
      nativeFilteredHorizontalCoordinates (I := I) Γ h) : χ g = χ h := by
  have hz : nativeFilteredHorizontalCoordinates (I := I) Γ (g*h⁻¹) = 0 := by
    rw [native_filtered_horizontal_coordinates_mul, heq,
      ← native_filtered_horizontal_coordinates_mul, mul_inv_cancel]
    funext i
    change (nativeLatticeFilteredSmoothRealBasis (I := I) Γ).repr
      (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) 1) i.val = 0
    rw [nativeLieGlobalLogarithm_one, map_zero]
    rfl
  have hc := native_additive_character_commutator χ hmul (g*h⁻¹)
    ((native_filtered_horizontal_coordinates_ker (I := I) Γ (g*h⁻¹)).mp hz)
  rw [hmul, native_additive_character_inv χ hmul] at hc
  linarith

theorem native_continuous_character_exponential_add (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (χ : G → ℝ)
    (hmul : ∀ g h, χ (g*h) = χ g + χ h) (v w : E) :
    χ (nativeLieExponential (I := I) (G := G) (v+w)) =
      χ (nativeLieExponential (I := I) (G := G) v) +
        χ (nativeLieExponential (I := I) (G := G) w) := by
  rw [← hmul]
  apply native_continuous_character_horizontal_fibers (I := I) Γ χ hmul
  rw [native_filtered_horizontal_coordinates_mul]
  funext i
  change (nativeLatticeFilteredSmoothRealBasis (I := I) Γ).repr
    (nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
      (nativeLieExponential (I := I) (G := G) (v+w))) i.val =
    (nativeLatticeFilteredSmoothRealBasis (I := I) Γ).repr
      (nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
        (nativeLieExponential (I := I) (G := G) v)) i.val +
    (nativeLatticeFilteredSmoothRealBasis (I := I) Γ).repr
      (nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
        (nativeLieExponential (I := I) (G := G) w)) i.val
  rw [nativeLieGlobalLogarithm_exponential, nativeLieGlobalLogarithm_exponential,
    nativeLieGlobalLogarithm_exponential, map_add, Finsupp.add_apply]

theorem native_continuous_character_linearization (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (χ : G → ℝ) (hcont : Continuous χ)
    (hmul : ∀ g h, χ (g*h) = χ g + χ h) :
    ∃! f : E →L[ℝ] ℝ, ∀ g, χ g = f (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g) := by
  let A : E →+ ℝ :=
    { toFun := fun v => χ (nativeLieExponential (I := I) (G := G) v)
      map_zero' := (congrArg χ (nativeLieExponential_zero (I := I) (G := G))).trans
        (native_additive_character_one χ hmul)
      map_add' := native_continuous_character_exponential_add (I := I) Γ χ hmul }
  have hA : Continuous A := hcont.comp (nativeLieExponential_continuous (I := I) (G := G))
  refine ⟨A.toRealLinearMap hA, ?_, ?_⟩
  · intro g
    change χ g = χ (nativeLieExponential (I := I) (G := G)
      (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g))
    rw [nativeLieExponential_globalLogarithm]
  · intro f hf
    ext v
    have h := hf (nativeLieExponential (I := I) (G := G) v)
    rw [nativeLieGlobalLogarithm_exponential] at h
    exact h.symm

end Hindman168
