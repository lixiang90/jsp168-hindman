import Hindman168.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The full OpenAI theorem statement and its implication for the prize target

The strong conclusion is a named proposition, not an axiom or proved claim.
The conditional implication below records exactly what remains to be supplied
by the paper's analytic argument.
-/

namespace Hindman168

open scoped BigOperators

/-- The paper's ordered, positive, rapidly separated monochromatic witness.
At the first index the preceding sum is zero and product is one, so the
separation condition reduces to `R < a 0`, as in the paper. -/
def StrongWitness {r m : ℕ} (color : ℕ → Fin r) (R D : ℝ) : Prop :=
  ∃ a : Fin m → ℕ, StrictMono a ∧ (∀ i, 0 < a i) ∧
    (∀ i, R * ((∑ j ∈ Finset.univ.filter (fun j : Fin m => j < i), (a j : ℝ)) +
      (∏ j ∈ Finset.univ.filter (fun j : Fin m => j < i), (a j : ℝ))) ^ D < (a i : ℝ)) ∧
    ∃ c : Fin r, ∀ S : Finset (Fin m), S.Nonempty →
      color (∑ i ∈ S, a i) = c ∧ color (∏ i ∈ S, a i) = c

/-- The main theorem claimed by the paper, with all quantifiers explicit. -/
def StrongConjecture : Prop :=
  ∀ (r : ℕ) (color : ℕ → Fin r) (m : ℕ) (R D : ℝ),
    2 ≤ R → 1 ≤ D → StrongWitness (m := m) color R D

theorem strong_to_indexed {r m : ℕ} {color : ℕ → Fin r} {R D : ℝ}
    (h : StrongWitness (m := m) color R D) : IndexedWitness (m := m) color := by
  obtain ⟨a, hstrict, hpos, _, c, hcolor⟩ := h
  exact ⟨a, hstrict.injective, hpos, c, hcolor⟩

/-- A completed proof of the strong paper theorem would solve the set target. -/
theorem strong_implies_finite (h : StrongConjecture) : FiniteConjecture := by
  intro r color m
  have hw := strong_to_indexed (h r color m 2 1 le_rfl le_rfl)
  obtain ⟨A, hcard, _, hmono⟩ := indexed_to_finset color hw
  exact ⟨A, hcard ▸ le_rfl, hmono⟩

/-- The precise bridge to google-deepmind/formal-conjectures' original target. -/
theorem strong_implies_subtype (h : StrongConjecture) : SubtypeConjecture :=
  finite_to_subtype (strong_implies_finite h)

end Hindman168
