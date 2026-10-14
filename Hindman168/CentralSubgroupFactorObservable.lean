import Hindman168.CentralSubgroupFactorFibers
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Analysis.Complex.Basic

/-! Continuous invariant observables descend to the ACTUAL image-lattice
central-subgroup factor, retaining all original point values. -/

namespace Hindman168
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (N Γ : Subgroup G) [N.Normal] (hN : N ≤ Subgroup.center G)

noncomputable def centralSubgroupFactorObservable (F : C(G ⧸ Γ, ℂ))
    (hF : ∀ (z : N) q, F ((z : G) • q) = F q) :
    C((G ⧸ N) ⧸ Γ.map (QuotientGroup.mk' N), ℂ) :=
  (central_subgroup_factor_map_openQuotient N Γ).isQuotientMap.lift
    (f := ⟨centralSubgroupFactorMap N Γ, (central_subgroup_factor_map_openQuotient N Γ).continuous⟩)
    F (by
      intro q r he
      obtain ⟨z,rfl⟩ := (central_subgroup_factor_fiber_iff N Γ hN q r).mp he
      exact (hF z q).symm)

theorem central_subgroup_factor_observable_apply (F : C(G ⧸ Γ, ℂ))
    (hF : ∀ (z : N) q, F ((z : G) • q) = F q) (q : G ⧸ Γ) :
    centralSubgroupFactorObservable N Γ hN F hF (centralSubgroupFactorMap N Γ q) = F q := by
  have h := (central_subgroup_factor_map_openQuotient N Γ).isQuotientMap.lift_comp
    (f := ⟨centralSubgroupFactorMap N Γ, (central_subgroup_factor_map_openQuotient N Γ).continuous⟩)
    F (by
      intro q r he
      obtain ⟨z,rfl⟩ := (central_subgroup_factor_fiber_iff N Γ hN q r).mp he
      exact (hF z q).symm)
  exact congrArg (fun K : C(G ⧸ Γ, ℂ) => K q) h

theorem central_subgroup_factor_observable_unique (F : C(G ⧸ Γ, ℂ))
    (hF : ∀ (z : N) q, F ((z : G) • q) = F q)
    (K : C((G ⧸ N) ⧸ Γ.map (QuotientGroup.mk' N), ℂ))
    (hK : ∀ q, K (centralSubgroupFactorMap N Γ q) = F q) :
    K = centralSubgroupFactorObservable N Γ hN F hF := by
  ext y
  obtain ⟨q,rfl⟩ := central_subgroup_factor_map_surjective N Γ y
  rw [hK,central_subgroup_factor_observable_apply]

theorem central_subgroup_factor_observable_bound (F : C(G ⧸ Γ, ℂ))
    (hF : ∀ (z : N) q, F ((z : G) • q) = F q) (B : ℝ) (hB : ∀ q, ‖F q‖ ≤ B) :
    ∀ y, ‖centralSubgroupFactorObservable N Γ hN F hF y‖ ≤ B := by
  intro y
  obtain ⟨q,rfl⟩ := central_subgroup_factor_map_surjective N Γ y
  rw [central_subgroup_factor_observable_apply]
  exact hB q

end Hindman168
