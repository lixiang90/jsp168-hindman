/-
Copyright OpenAI contributors. Licensed under Apache-2.0; see dependencies/openai-finite-szemeredi/LICENSE.
Original source: openai/math commit adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Modified for Lean 4.32.2 / mathlib 905b958 compatibility.
Original hashes and exact compatibility changes:
dependencies/openai-finite-szemeredi/NATIVE-INVERSE-SOURCE-MANIFEST.json.
-/
import OAI.Combinatorics.Progressions.Estimates.PrincipalBlockExponent

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem monomialScale_productBlockExponent {K : Type*} {h : ℕ}
    (principal : Fin h → K) (T : K → ℝ) :
    monomialScale T (productBlockExponent principal) = ∏ v, T (principal v) := by
  have he := congrArg (MvPolynomial.eval T) (productBlockExponent_monomial principal (1 : ℝ))
  simpa only [MvPolynomial.eval_monomial, one_mul, map_mul, map_prod, MvPolynomial.eval_C,
    MvPolynomial.eval_X, Finsupp.prod, monomialScale] using he

theorem monomialScale_canonicalPrincipal {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (T : SamplerTupleIndex G B h → ℝ) (d : D) (b : B d) :
    monomialScale T (canonicalPrincipalExponent h d b) = ∏ v, T (.inr ⟨d, b, v⟩) :=
  monomialScale_productBlockExponent _ T

end Erdos3

end

end OAI
