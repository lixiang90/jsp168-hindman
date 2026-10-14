import Hindman168.CentralFactorCosetFibers
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Analysis.Complex.Basic

/-! Genuine continuous descent of central-invariant ORIGINAL observables. -/

namespace Hindman168

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

noncomputable def centralFactorObservable (Γ : Subgroup G) (F : C(G ⧸ Γ, ℂ))
    (hF : ∀ (z : Subgroup.center G) q, F ((z : G) • q) = F q) :
    C((G ⧸ Subgroup.center G) ⧸ Γ.map (QuotientGroup.mk' (Subgroup.center G)), ℂ) :=
  (central_factor_coset_map_openQuotient Γ).isQuotientMap.lift
    (f := ⟨centralFactorCosetMap Γ, central_factor_coset_map_continuous Γ⟩) F (by
    intro q r h
    obtain ⟨z, rfl⟩ := (central_factor_coset_map_fiber_iff Γ q r).mp h
    exact (hF z q).symm)

theorem central_factor_observable_apply (Γ : Subgroup G) (F : C(G ⧸ Γ, ℂ))
    (hF : ∀ (z : Subgroup.center G) q, F ((z : G) • q) = F q) (q : G ⧸ Γ) :
    centralFactorObservable Γ F hF (centralFactorCosetMap Γ q) = F q := by
  have h := (central_factor_coset_map_openQuotient Γ).isQuotientMap.lift_comp
    (f := ⟨centralFactorCosetMap Γ, central_factor_coset_map_continuous Γ⟩) F (by
    intro q r h
    obtain ⟨z, rfl⟩ := (central_factor_coset_map_fiber_iff Γ q r).mp h
    exact (hF z q).symm)
  exact congrArg (fun K : C(G ⧸ Γ, ℂ) => K q) h

theorem central_factor_observable_unique (Γ : Subgroup G) (F : C(G ⧸ Γ, ℂ))
    (hF : ∀ (z : Subgroup.center G) q, F ((z : G) • q) = F q)
    (K : C((G ⧸ Subgroup.center G) ⧸ Γ.map (QuotientGroup.mk' (Subgroup.center G)), ℂ))
    (hK : ∀ q, K (centralFactorCosetMap Γ q) = F q) :
    K = centralFactorObservable Γ F hF := by
  ext y
  obtain ⟨q, rfl⟩ := central_factor_coset_map_surjective Γ y
  rw [hK, central_factor_observable_apply]

theorem central_factor_observable_point_bound (Γ : Subgroup G) (F : C(G ⧸ Γ, ℂ))
    (hF : ∀ (z : Subgroup.center G) q, F ((z : G) • q) = F q)
    (B : ℝ) (hB : ∀ q, ‖F q‖ ≤ B) :
    ∀ y, ‖centralFactorObservable Γ F hF y‖ ≤ B := by
  intro y
  obtain ⟨q, rfl⟩ := central_factor_coset_map_surjective Γ y
  rw [central_factor_observable_apply]
  exact hB q

end Hindman168
