import Hindman168.NativeLieLogarithmCharacter
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Instances.Real.Lemmas

/-! Actual real logarithmic characters descend through the original
coset quotient of any specified subgroup they annihilate. Compactness of
that actual quotient forces the character functional to vanish. No normality
of the specified subgroup is needed. -/

namespace Hindman168
open Function Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeLieLogarithmCharacterQuotient (Γ : Subgroup G) (f : E →ₗ[ℝ] ℝ)
    (hcomm : nativeLieLowerCentralModel (I := I) (G := G) 1 ≤ f.ker)
    (hΓ : ∀ g ∈ Γ, f (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g) = 0) :
    C(G ⧸ Γ, ℝ) := by
  let χ : C(G, ℝ) := nativeLieLogarithmCharacter (I := I) (G := G) f
  let q : G ⧸ Γ → ℝ := Quotient.lift (fun g : G => χ g) (by
    intro a b hab
    have hm : a⁻¹ * b ∈ Γ := (QuotientGroup.leftRel_apply).mp hab
    have hz : χ (a⁻¹ * b) = 0 := hΓ _ hm
    have he := nativeLieLogarithmCharacter_mul (I := I) (G := G) f hcomm a (a⁻¹ * b)
    change χ (a * (a⁻¹ * b)) = χ a + χ (a⁻¹ * b) at he
    rw [mul_inv_cancel_left, hz, add_zero] at he
    exact he.symm)
  refine ⟨q, ?_⟩
  exact (QuotientGroup.isQuotientMap_mk Γ).continuous_iff.mpr χ.continuous

 theorem nativeLieLogarithmCharacterQuotient_mk (Γ : Subgroup G) (f : E →ₗ[ℝ] ℝ)
    (hcomm : nativeLieLowerCentralModel (I := I) (G := G) 1 ≤ f.ker)
    (hΓ : ∀ g ∈ Γ, f (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g) = 0) (g : G) :
    nativeLieLogarithmCharacterQuotient Γ f hcomm hΓ (QuotientGroup.mk g) =
      nativeLieLogarithmCharacter (I := I) (G := G) f g := rfl

 theorem nativeLieLogarithmFunctional_eq_zero_of_compact_quotient
    (Γ : Subgroup G) [CompactSpace (G ⧸ Γ)] (f : E →ₗ[ℝ] ℝ)
    (hcomm : nativeLieLowerCentralModel (I := I) (G := G) 1 ≤ f.ker)
    (hΓ : ∀ g ∈ Γ, f (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g) = 0) :
    f = 0 := by
  by_contra hf
  let q : C(G ⧸ Γ, ℝ) := nativeLieLogarithmCharacterQuotient Γ f hcomm hΓ
  have hs : Surjective q := by
    intro r
    obtain ⟨g, hg⟩ := nativeLieLogarithmCharacter_surjective (I := I) (G := G) f hf r
    exact ⟨QuotientGroup.mk g, hg⟩
  have hc := isCompact_range q.continuous
  rw [range_eq_univ.mpr hs] at hc
  exact noncompact_univ ℝ hc

end Hindman168
