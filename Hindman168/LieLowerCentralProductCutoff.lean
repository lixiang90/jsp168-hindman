import Mathlib.Algebra.Lie.Nilpotent

/-! Products of the actual Lie action control the actual lower central
series. This algebraic lemma will be instantiated with derivatives of
original group commutator words, rather than a supplied Lie-nilpotency
premise. -/

namespace Hindman168
open Module

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

 theorem lie_lowerCentral_eq_bot_of_action_products_zero (k : ℕ)
    (hk : ∀ xs : List L, xs.length = k →
      (xs.map (LieModule.toEnd R L M)).prod = 0) :
    LieModule.lowerCentralSeries R L M k = ⊥ := by
  have ha : ∀ j : ℕ, ∀ xs : List L, xs.length + j = k →
      (LieModule.lowerCentralSeries R L M j : Submodule R M) ≤
        LinearMap.ker (xs.map (LieModule.toEnd R L M)).prod := by
    intro j
    induction j with
    | zero =>
      intro xs hxs
      have hlen : xs.length = k := by simpa using hxs
      rw [hk xs hlen]
      simp
    | succ j ih =>
      intro xs hxs
      rw [LieModule.lowerCentralSeries_succ, LieSubmodule.lieIdeal_oper_eq_linear_span']
      apply Submodule.span_le.mpr
      rintro y ⟨u, _, z, hz, rfl⟩
      have hlen : (xs ++ [u]).length + j = k := by
        simp only [List.length_append, List.length_singleton]
        omega
      have h := ih (xs ++ [u]) hlen hz
      rw [LinearMap.mem_ker] at h
      change (xs.map (LieModule.toEnd R L M)).prod ⁅u, z⁆ = 0
      simpa only [List.map_append, List.prod_append, List.map_singleton,
        List.prod_singleton, Module.End.mul_apply, LieModule.toEnd_apply_apply] using h
  apply le_antisymm _ bot_le
  intro x hx
  have h := ha k [] (by simp) hx
  simpa only [List.map_nil, List.prod_nil, LinearMap.mem_ker, Module.End.one_apply,
    LieSubmodule.mem_bot] using h

 theorem lie_isNilpotent_of_action_products_zero (k : ℕ)
    (hk : ∀ xs : List L, xs.length = k →
      (xs.map (LieModule.toEnd R L M)).prod = 0) :
    LieModule.IsNilpotent L M :=
  LieModule.IsNilpotent.mk (M := M) (lie_lowerCentral_eq_bot_of_action_products_zero k hk)

end Hindman168
