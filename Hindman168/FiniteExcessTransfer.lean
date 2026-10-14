import Hindman168.LocalExcessProducts
import Hindman168.FiniteProductExpectations

/-!
# Actual bounded excess transfer between prime-parameter laws

For fixed bounded divisor valuations, the beta product is bounded by V^q
under every prime-parameter outcome, even outside the row domain. Thus
changing the prime law costs V^q times its L1 distance. Actual restricted
alpha excess is nonnegative and dominated by the beta product before
that change of law, with no normalization by the event probability.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

noncomputable def localExcessBetaProduct {ι α : Type*} [Fintype ι]
    (p : ι → ℕ) {q : ℕ} (a : ι → Fin q → ℕ) (bad : ι → α → Prop) (x : α) : ℝ :=
  (∏ i, (1 + localExcessBeta (p i) (a i) (bad i x))) - 1

theorem localExcessBetaProduct_bounded {ι α : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] {q : ℕ} (a : ι → Fin q → ℕ)
    (bad : ι → α → Prop) (V : ℕ) (hV : ∀ u, (∏ i, p i ^ a i u) ≤ V) (x : α) :
    0 ≤ localExcessBetaProduct p a bad x ∧ localExcessBetaProduct p a bad x ≤ ((V ^ q : ℕ) : ℝ) := by
  have h := localExcessBeta_product_bound p a (fun i => bad i x)
  exact ⟨h.1, h.2.trans (factored_row_divisor_product_le p a V hV)⟩

theorem localExcessBetaProduct_expectation_transfer {ι α : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] {q : ℕ} (a : ι → Fin q → ℕ)
    (bad : ι → α → Prop) (V : ℕ) (hV : ∀ u, (∏ i, p i ^ a i u) ≤ V)
    (μ ν : Mass α) :
    |expectation μ (localExcessBetaProduct p a bad) - expectation ν (localExcessBetaProduct p a bad)| ≤
      ((V ^ q : ℕ) : ℝ) * distance μ ν := by
  apply expectation_difference_bound
  intro x
  have h := localExcessBetaProduct_bounded p a bad V hV x
  rw [abs_of_nonneg h.1]
  exact h.2

theorem restricted_localAlpha_excess_expectation_transfer {ι α : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] (hp : ∀ i, (p i).Prime)
    (q d : ℕ) (A : ι → ℕ) (a : ι → Fin q → ℕ) (ha : ∀ i u, a i u ≤ A i)
    (c : α → Fin q → Fin d → ℤ) (bad : ι → α → Prop) (E : α → Prop)
    (hprimitive : ∀ x, E x → ∀ i u, ∃ j, (c x u j : ZMod (p i)) ≠ 0)
    (hindependent : ∀ x, E x → ∀ i, ¬ bad i x → ∀ u v, u ≠ v → LinearIndependent (ZMod (p i))
      ![(fun j => (c x u j : ZMod (p i))), (fun j => (c x v j : ZMod (p i)))])
    (V : ℕ) (hV : ∀ u, (∏ i, p i ^ a i u) ≤ V) (μ ν : Mass α) (hμ : ∀ x, 0 ≤ μ x) :
    0 ≤ expectation μ (fun x => if E x then
      (∏ i, primePowerLocalAlpha (p i) q d (A i) (a i) (ha i) (c x)) - 1 else 0) ∧
      expectation μ (fun x => if E x then
        (∏ i, primePowerLocalAlpha (p i) q d (A i) (a i) (ha i) (c x)) - 1 else 0) ≤
        expectation ν (localExcessBetaProduct p a bad) + ((V ^ q : ℕ) : ℝ) * distance μ ν := by
  let f : α → ℝ := fun x => if E x then
    (∏ i, primePowerLocalAlpha (p i) q d (A i) (a i) (ha i) (c x)) - 1 else 0
  have hpoint (x : α) : 0 ≤ f x ∧ f x ≤ localExcessBetaProduct p a bad x :=
    primePowerLocalAlpha_product_excess p hp q d A a ha (c x) (fun i => bad i x) (E x)
      (hprimitive x) (hindependent x)
  have h0 := expectation_nonneg μ f hμ (fun x => (hpoint x).1)
  have hdom := expectation_mono μ f (localExcessBetaProduct p a bad) hμ (fun x => (hpoint x).2)
  have htransfer := localExcessBetaProduct_expectation_transfer p a bad V hV μ ν
  have hle := (le_abs_self (expectation μ (localExcessBetaProduct p a bad) -
    expectation ν (localExcessBetaProduct p a bad))).trans htransfer
  exact ⟨h0, by linarith⟩

end Hindman168
