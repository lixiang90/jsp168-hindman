import Hindman168.FinalStrongFromOpenAI

/-!
Explicit JSP-000168 library statement for Lake DAG verification.

The proof uses the existing `strong_to_indexed` and `indexed_to_finset`
reductions after the fixed OpenAI inverse assembly. Verification status is
recorded in `verification/original-final-target`; the full chain must be
built and audited before any completion claim. It is not imported by the old
canonical aggregate. Do not import its preserved work-in-progress snapshot
in the same environment, since the theorem names coincide.
-/

namespace Hindman168
open scoped BigOperators

/-- Every finite coloring admits exactly `m` distinct positive integers whose
nonempty subset sums and products all have one common color. -/
theorem jsp000168_from_openai :
    ∀ (r : ℕ) (χ : ℕ → Fin r) (m : ℕ),
      ∃ (A : Finset ℕ) (c : Fin r),
        A.card = m ∧ (∀ a ∈ A, 0 < a) ∧
          ∀ B : Finset ℕ, B ⊆ A → B.Nonempty →
            χ (∑ b ∈ B, b) = c ∧ χ (∏ b ∈ B, b) = c := by
  intro r χ m
  have hindexed := strong_to_indexed
    (strongConjecture_from_openai r χ m 2 1 le_rfl le_rfl)
  obtain ⟨A, hcard, hpositive, c, hmonochromatic⟩ := indexed_to_finset χ hindexed
  exact ⟨A, c, hcard, hpositive, hmonochromatic⟩

/-
Statement vocabulary review (source-level checks, not compilation evidence):

* `χ : ℕ → Fin r` is an arbitrary total coloring with a finite color type.
* `A : Finset ℕ` has no repeated elements, and `A.card = m` is exact size.
* `∀ a ∈ A, 0 < a` explicitly removes zero from the witness.
* `B ⊆ A` ranges over all finite subsets of that same witness.
* `B.Nonempty` excludes the empty sum and empty product.
* Mathlib's finite sum and product are taken in `ℕ`, using each member once.
* A single `c : Fin r` is fixed before every subset and both operations.
* `r = 0` has no coloring `ℕ → Fin 0`; its universally quantified case is
  vacuous. `m = 0` allows the empty witness with vacuous subset conditions.
-/

end Hindman168
