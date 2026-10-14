/-
Copyright OpenAI contributors. Licensed under Apache-2.0; see dependencies/openai-finite-szemeredi/LICENSE.
Original source: openai/math commit adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Modified for Lean 4.32.2 / mathlib 905b958 compatibility.
Original hashes and exact compatibility changes:
dependencies/openai-finite-szemeredi/NATIVE-INVERSE-SOURCE-MANIFEST.json.
-/
import OAI.Combinatorics.Progressions.Polynomial.RawCanonicalNormalizedPolynomial

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def productBlockExponent {K : Type*} {h : ℕ} (principal : Fin h → K) : K →₀ ℕ :=
  ∑ v, Finsupp.single (principal v) 1

theorem productBlockExponent_monomial {K : Type*} {h : ℕ}
    (principal : Fin h → K) (c : ℝ) :
    MvPolynomial.monomial (productBlockExponent principal) c =
      MvPolynomial.C c * ∏ v, MvPolynomial.X (principal v) := by
  rw [productBlockExponent, MvPolynomial.monomial_sum_index]
  rfl

noncomputable def canonicalPrincipalExponent {D G : Type*} {B : D → Type*} (h : D → ℕ)
    (d : D) (b : B d) : SamplerTupleIndex G B h →₀ ℕ :=
  productBlockExponent (fun v => .inr ⟨d, b, v⟩)

theorem canonicalPrincipalExponent_apply {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) [DecidableEq (B d)] (b b' : B d) (v : Fin (h d)) :
    canonicalPrincipalExponent (G := G) h d b (.inr ⟨d, b', v⟩) = if b = b' then 1 else 0 := by
  classical
  by_cases hb : b = b' <;>
    simp [canonicalPrincipalExponent, productBlockExponent, Finsupp.single_apply, hb]

theorem canonicalPrincipalExponent_ne_zero {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) (hd : 0 < h d) (b : B d) :
    canonicalPrincipalExponent (G := G) h d b ≠ 0 := by
  classical
  intro he
  have hv := congrArg (fun e : SamplerTupleIndex G B h →₀ ℕ => e (.inr ⟨d, b, ⟨0, hd⟩⟩)) he
  simp [canonicalPrincipalExponent_apply] at hv

theorem canonicalPrincipalExponent_injective {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) (hd : 0 < h d) :
    Function.Injective (canonicalPrincipalExponent (G := G) (B := B) h d) := by
  classical
  intro b b' he
  by_contra hne
  have hv := congrArg (fun e : SamplerTupleIndex G B h →₀ ℕ => e (.inr ⟨d, b', ⟨0, hd⟩⟩)) he
  simp [canonicalPrincipalExponent_apply, hne] at hv

end Erdos3

end

end OAI
