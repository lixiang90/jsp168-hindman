import Hindman168.NativeLatticeOrderedDiffeomorph
import Hindman168.NativeOrderedCharacterEvaluation

/-! For the SAME fixed smooth lattice-coordinate basis, killing the actual
commutator layer makes lattice integrality equivalent to integer values
on the basis. No additive-lattice assertion about Log Gamma is used. -/

namespace Hindman168
open scoped BigOperators Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem native_smooth_basis_character_evaluation (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (f : E →ₗ[ℝ] ℝ)
    (hf : nativeLieLowerCentralModel (I := I) (G := G) 1 ≤ f.ker)
    (x : Fin (Module.finrank ℝ E) → ℝ) :
    nativeLieLogarithmCharacter (I := I) (G := G) f
      (nativeLatticeOrderedDiffeomorph (I := I) Γ x) =
      ∑ i, x i * f (nativeLatticeOrderedSmoothRealBasis (I := I) Γ i) :=
  native_ordered_character_evaluation f hf _ x

theorem native_smooth_basis_character_inverse_evaluation (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (f : E →ₗ[ℝ] ℝ)
    (hf : nativeLieLowerCentralModel (I := I) (G := G) 1 ≤ f.ker) (g : G) :
    nativeLieLogarithmCharacter (I := I) (G := G) f g =
      ∑ i, (nativeLatticeOrderedDiffeomorph (I := I) Γ).symm g i *
        f (nativeLatticeOrderedSmoothRealBasis (I := I) Γ i) := by
  have h := native_smooth_basis_character_evaluation Γ f hf
    ((nativeLatticeOrderedDiffeomorph (I := I) Γ).symm g)
  rw [Diffeomorph.apply_symm_apply] at h
  exact h

theorem native_smooth_basis_character_integral_iff (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (f : E →ₗ[ℝ] ℝ)
    (hf : nativeLieLowerCentralModel (I := I) (G := G) 1 ≤ f.ker) :
    (∀ γ ∈ Γ, ∃ n : ℤ, nativeLieLogarithmCharacter (I := I) (G := G) f γ = (n : ℝ)) ↔
      ∀ i, ∃ n : ℤ, f (nativeLatticeOrderedSmoothRealBasis (I := I) Γ i) = (n : ℝ) := by
  constructor
  · intro h i
    have hi := h _ (native_lattice_ordered_smooth_basis_exponential_mem (I := I) Γ i)
    simpa only [nativeLieLogarithmCharacter_exponential] using hi
  · intro h γ hγ
    classical
    let x := (nativeLatticeOrderedDiffeomorph (I := I) Γ).symm γ
    have hx : ∀ i, ∃ n : ℤ, x i = (n : ℝ) := by
      apply (native_lattice_ordered_diffeomorph_mem_iff (I := I) Γ x).mp
      simpa only [x, Diffeomorph.apply_symm_apply] using hγ
    choose n hn using hx
    choose a ha using h
    refine ⟨∑ i, n i * a i, ?_⟩
    rw [native_smooth_basis_character_inverse_evaluation Γ f hf γ]
    change (∑ i, x i * f (nativeLatticeOrderedSmoothRealBasis (I := I) Γ i)) = _
    simp only [hn, ha, Int.cast_sum, Int.cast_mul]

end Hindman168
