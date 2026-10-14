import Hindman168.LocalExcessBeta

/-!
# Pointwise product excess and arbitrary prime-only restrictions

The true local alpha factors are at least one everywhere. Their beta
majorants are nonnegative even outside the row domain, so an arbitrary
subevent can be dropped from the upper bound. The complete majorant is
bounded by the product of the actual factored row divisors, and hence by
V^q while those divisors are bounded by V.
-/

namespace Hindman168

open scoped BigOperators Classical

theorem prod_excess_indicator_domination {ι : Type*} [Fintype ι]
    (α β : ι → ℝ) (E : Prop) (hα : ∀ i, 1 ≤ α i) (hβ : ∀ i, 0 ≤ β i)
    (hdom : E → ∀ i, α i - 1 ≤ β i) :
    0 ≤ (if E then (∏ i, α i) - 1 else 0) ∧
      (if E then (∏ i, α i) - 1 else 0) ≤ (∏ i, (1 + β i)) - 1 := by
  have hαprod : 1 ≤ ∏ i, α i := Finset.one_le_prod (fun i _ => hα i)
  have hβprod : 1 ≤ ∏ i, (1 + β i) := Finset.one_le_prod (fun i _ => by linarith [hβ i])
  by_cases he : E
  · have hle : (∏ i, α i) ≤ ∏ i, (1 + β i) := Finset.prod_le_prod
      (fun i _ => by linarith [hα i]) (fun i _ => by linarith [hdom he i])
    simp only [if_pos he]
    constructor <;> linarith
  · simp only [if_neg he]
    constructor <;> linarith

theorem localExcessBeta_product_bound {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] {q : ℕ}
    (a : ι → Fin q → ℕ) (bad : ι → Prop) :
    0 ≤ (∏ i, (1 + localExcessBeta (p i) (a i) (bad i))) - 1 ∧
      (∏ i, (1 + localExcessBeta (p i) (a i) (bad i))) - 1 ≤
        ((∏ u, ∏ i, p i ^ a i u : ℕ) : ℝ) := by
  have h1 : 1 ≤ ∏ i, (1 + localExcessBeta (p i) (a i) (bad i)) :=
    Finset.one_le_prod (fun i _ => by linarith [localExcessBeta_nonneg (p i) (a i) (bad i)])
  have h2 : (∏ i, (1 + localExcessBeta (p i) (a i) (bad i))) ≤
      ∏ i, ((p i ^ (∑ u, a i u) : ℕ) : ℝ) :=
    Finset.prod_le_prod (fun i _ => by linarith [localExcessBeta_nonneg (p i) (a i) (bad i)])
      (fun i _ => one_add_localExcessBeta_le (p i) (a i) (bad i))
  have hn : ((∏ u, ∏ i, p i ^ a i u : ℕ) : ℝ) = ∏ i, ((p i ^ (∑ u, a i u) : ℕ) : ℝ) := by
    rw [rowPrimePower_divisor_product, Nat.cast_prod]
  rw [← hn] at h2
  constructor <;> linarith

theorem factored_row_divisor_product_le {ι : Type*} [Fintype ι]
    (p : ι → ℕ) {q : ℕ} (a : ι → Fin q → ℕ) (V : ℕ)
    (hV : ∀ u, (∏ i, p i ^ a i u) ≤ V) :
    ((∏ u, ∏ i, p i ^ a i u : ℕ) : ℝ) ≤ ((V ^ q : ℕ) : ℝ) := by
  have h : (∏ u, ∏ i, p i ^ a i u) ≤ ∏ _u : Fin q, V :=
    Finset.prod_le_prod' (fun u _ => hV u)
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (show ((∏ u, ∏ i, p i ^ a i u : ℕ) : ℝ) ≤ ((∏ _u : Fin q, V : ℕ) : ℝ) from by exact_mod_cast h)

theorem primePowerLocalAlpha_product_excess {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] (hp : ∀ i, (p i).Prime)
    (q d : ℕ) (A : ι → ℕ) (a : ι → Fin q → ℕ) (ha : ∀ i u, a i u ≤ A i)
    (c : Fin q → Fin d → ℤ) (bad : ι → Prop) (E : Prop)
    (hprimitive : E → ∀ i u, ∃ j, (c u j : ZMod (p i)) ≠ 0)
    (hindependent : E → ∀ i, ¬ bad i → ∀ u v, u ≠ v → LinearIndependent (ZMod (p i))
      ![(fun j => (c u j : ZMod (p i))), (fun j => (c v j : ZMod (p i)))]) :
    0 ≤ (if E then (∏ i, primePowerLocalAlpha (p i) q d (A i) (a i) (ha i) c) - 1 else 0) ∧
      (if E then (∏ i, primePowerLocalAlpha (p i) q d (A i) (a i) (ha i) c) - 1 else 0) ≤
        (∏ i, (1 + localExcessBeta (p i) (a i) (bad i))) - 1 := by
  apply prod_excess_indicator_domination
  · intro i
    exact (primePowerLocalAlpha_bounds (p i) q d (A i) (a i) (ha i) c).1
  · intro i
    exact localExcessBeta_nonneg (p i) (a i) (bad i)
  · intro he i
    exact (primePowerLocalAlpha_excess_le_beta (p i) q d (A i) (hp i) (a i) (ha i) c (bad i)
      (hprimitive he i) (hindependent he i)).2

theorem primePowerLocalAlpha_product_excess_bounded {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] (hp : ∀ i, (p i).Prime)
    (q d : ℕ) (A : ι → ℕ) (a : ι → Fin q → ℕ) (ha : ∀ i u, a i u ≤ A i)
    (c : Fin q → Fin d → ℤ) (bad : ι → Prop) (E : Prop)
    (hprimitive : E → ∀ i u, ∃ j, (c u j : ZMod (p i)) ≠ 0)
    (hindependent : E → ∀ i, ¬ bad i → ∀ u v, u ≠ v → LinearIndependent (ZMod (p i))
      ![(fun j => (c u j : ZMod (p i))), (fun j => (c v j : ZMod (p i)))])
    (V : ℕ) (hV : ∀ u, (∏ i, p i ^ a i u) ≤ V) :
    0 ≤ (if E then (∏ i, primePowerLocalAlpha (p i) q d (A i) (a i) (ha i) c) - 1 else 0) ∧
      (if E then (∏ i, primePowerLocalAlpha (p i) q d (A i) (a i) (ha i) c) - 1 else 0) ≤
        ((V ^ q : ℕ) : ℝ) := by
  have h := primePowerLocalAlpha_product_excess p hp q d A a ha c bad E hprimitive hindependent
  exact ⟨h.1, h.2.trans ((localExcessBeta_product_bound p a bad).2.trans
    (factored_row_divisor_product_le p a V hV))⟩

end Hindman168
