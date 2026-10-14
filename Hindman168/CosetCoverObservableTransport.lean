import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Complex.Basic
import Hindman168.FiniteComplexMean

/-! Actual observable transport along a homomorphism of coset spaces.

The subgroups need not be normal. The map is constructed from the group
homomorphism and lattice containment; its orbit identity is proved rather
than assumed. Metric Lipschitz bounds are propagated from a supplied bound
on this actual map. Establishing that bound for a particular geometric
cover remains a separate obligation, supplied by the corresponding metric
construction, not by this transport lemma.
-/

namespace Hindman168

open scoped NNReal

variable {G H : Type*} [Group G] [Group H]
  (Γ : Subgroup G) (Λ : Subgroup H) (f : G →* H)
  (hfΓ : Γ ≤ Λ.comap f)

def cosetCoverMap : G ⧸ Γ → H ⧸ Λ :=
  Quotient.lift (fun g : G => (f g : H ⧸ Λ)) (by
    intro a b hab
    apply QuotientGroup.eq.mpr
    have h := hfΓ (QuotientGroup.leftRel_apply.mp hab)
    change f (a⁻¹ * b) ∈ Λ at h
    simpa only [map_mul, map_inv] using h)

theorem cosetCoverMap_mk (g : G) :
    cosetCoverMap Γ Λ f hfΓ (g : G ⧸ Γ) = (f g : H ⧸ Λ) := rfl

theorem cosetCoverMap_linearOrbit (g x : G) (n : ℤ) :
    cosetCoverMap Γ Λ f hfΓ ((g ^ n * x : G) : G ⧸ Γ) =
      (((f g) ^ n * f x : H) : H ⧸ Λ) := by
  simp only [cosetCoverMap_mk, map_mul, map_zpow]

theorem cosetCoverMap_surjective (hf : Function.Surjective f) :
    Function.Surjective (cosetCoverMap Γ Λ f hfΓ) := by
  intro y
  refine Quotient.inductionOn y ?_
  intro h
  obtain ⟨g, rfl⟩ := hf h
  exact ⟨(g : G ⧸ Γ), rfl⟩

section Topology

variable [TopologicalSpace G] [TopologicalSpace H]

theorem cosetCoverMap_continuous (hf : Continuous f) :
    Continuous (cosetCoverMap Γ Λ f hfΓ) := by
  apply (QuotientGroup.isQuotientMap_mk Γ).continuous_iff.mpr
  exact QuotientGroup.continuous_mk.comp hf

noncomputable def cosetCoverObservable (hf : Continuous f) (obs : C(H ⧸ Λ, ℂ)) : C(G ⧸ Γ, ℂ) :=
  obs.comp ⟨cosetCoverMap Γ Λ f hfΓ, cosetCoverMap_continuous Γ Λ f hfΓ hf⟩

theorem cosetCoverObservable_norm_le (hf : Continuous f) (obs : C(H ⧸ Λ, ℂ))
    (C : ℝ) (hobs : ∀ z, ‖obs z‖ ≤ C) (z : G ⧸ Γ) :
    ‖cosetCoverObservable Γ Λ f hfΓ hf obs z‖ ≤ C :=
  hobs _

theorem cosetCoverObservable_linearOrbit (hf : Continuous f) (obs : C(H ⧸ Λ, ℂ))
    (g x : G) (n : ℤ) :
    cosetCoverObservable Γ Λ f hfΓ hf obs ((g ^ n * x : G) : G ⧸ Γ) =
      obs ((((f g) ^ n * f x : H) : H ⧸ Λ)) := by
  exact congrArg obs (cosetCoverMap_linearOrbit Γ Λ f hfΓ g x n)

theorem cosetCoverObservable_correlation (hf : Continuous f) (obs : C(H ⧸ Λ, ℂ))
    (g x : G) (L : ℕ) (v : Fin L → ℂ) :
    finiteComplexMean (fun n => v n *
      cosetCoverObservable Γ Λ f hfΓ hf obs ((g ^ (n.val : ℤ) * x : G) : G ⧸ Γ)) =
    finiteComplexMean (fun n => v n * obs
      ((((f g) ^ (n.val : ℤ) * f x : H) : H ⧸ Λ))) := by
  congr 1
  funext n
  rw [cosetCoverObservable_linearOrbit]

end Topology

section Metric

variable [MetricSpace (G ⧸ Γ)] [MetricSpace (H ⧸ Λ)]

/-- Propagate a proved metric bound on the actual cover map. -/
theorem cosetCoverMap_lipschitz_observable {K J : ℝ≥0}
    (hmap : LipschitzWith J (cosetCoverMap Γ Λ f hfΓ))
    (obs : H ⧸ Λ → ℂ) (hobs : LipschitzWith K obs) :
    LipschitzWith (K * J) (obs ∘ cosetCoverMap Γ Λ f hfΓ) :=
  hobs.comp hmap

/-- A surjective group homomorphism lifts the actual linear nilsequence
to the cover, with unchanged values and an explicit Lipschitz multiplier.
This theorem does not assume either lattice is normal. -/
theorem exists_cosetCoverObservable_lift {K J : ℝ≥0}
    (hf : Function.Surjective f)
    (hmap : LipschitzWith J (cosetCoverMap Γ Λ f hfΓ))
    (obs : C(H ⧸ Λ, ℂ)) (hobs : LipschitzWith K obs)
    (hbound : ∀ z, ‖obs z‖ ≤ 1) (g₀ x₀ : H) :
    ∃ (lifted : C(G ⧸ Γ, ℂ)) (g x : G),
      (∀ z, ‖lifted z‖ ≤ 1) ∧ LipschitzWith (K * J) lifted ∧
      ∀ n : ℤ, lifted ((g ^ n * x : G) : G ⧸ Γ) =
        obs ((g₀ ^ n * x₀ : H) : H ⧸ Λ) := by
  obtain ⟨g, rfl⟩ := hf g₀
  obtain ⟨x, rfl⟩ := hf x₀
  let lifted : C(G ⧸ Γ, ℂ) :=
    obs.comp ⟨cosetCoverMap Γ Λ f hfΓ, hmap.continuous⟩
  refine ⟨lifted, g, x, ?_, ?_, ?_⟩
  · intro z
    exact hbound _
  · exact hobs.comp hmap
  · intro n
    exact congrArg obs (cosetCoverMap_linearOrbit Γ Λ f hfΓ g x n)

end Metric

end Hindman168
