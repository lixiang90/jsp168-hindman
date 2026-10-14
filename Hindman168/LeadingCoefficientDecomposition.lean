import Hindman168.DyadicPrimeRelabeling

/-!
# Exact exceptional-event split for the rough-coprimality induction

Zero specialized leading coefficients are separated first. A common
prime dividing either nonzero leading coefficient belongs to the smaller
polynomial pair. All remaining primes belong to the proved regular event.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem commonPrimeEvent_leading_decomposition {m n w : ℕ}
    (F : MvPolynomial (Fin (m + 1)) ℤ) (G : MvPolynomial (Fin (n + 1)) ℤ)
    (xy : (Fin (m + 1) → ℕ) × (Fin (n + 1) → ℕ))
    (h : commonPrimeEvent w F G xy) :
    MvPolynomial.eval (fun i => (Fin.tail xy.1 i : ℤ)) (integerPolynomialMainLeading F) = 0 ∨
      MvPolynomial.eval (fun i => (Fin.tail xy.2 i : ℤ)) (integerPolynomialMainLeading G) = 0 ∨
      commonPrimeEvent w (integerPolynomialMainLeading F) G (Fin.tail xy.1, xy.2) ∨
      commonPrimeEvent w F (integerPolynomialMainLeading G) (xy.1, Fin.tail xy.2) ∨
      regularCommonPrimeEvent w F G xy := by
  rcases h with ⟨hF, hG, q, hq, hwq, hqF, hqG⟩
  by_cases hA : MvPolynomial.eval (fun i => (Fin.tail xy.1 i : ℤ)) (integerPolynomialMainLeading F) = 0
  · exact Or.inl hA
  apply Or.inr
  by_cases hB : MvPolynomial.eval (fun i => (Fin.tail xy.2 i : ℤ)) (integerPolynomialMainLeading G) = 0
  · exact Or.inl hB
  apply Or.inr
  by_cases hqA : (q : ℤ) ∣ MvPolynomial.eval (fun i => (Fin.tail xy.1 i : ℤ)) (integerPolynomialMainLeading F)
  · exact Or.inl ⟨hA, hG, q, hq, hwq, hqA, hqG⟩
  apply Or.inr
  by_cases hqB : (q : ℤ) ∣ MvPolynomial.eval (fun i => (Fin.tail xy.2 i : ℤ)) (integerPolynomialMainLeading G)
  · exact Or.inl ⟨hF, hB, q, hq, hwq, hqF, hqB⟩
  exact Or.inr ⟨hF, q, hq, hwq, ⟨hqA, hqF⟩, hqB, hqG⟩

theorem commonPrimeEvent_leading_probability_split {m n w : ℕ}
    (F : MvPolynomial (Fin (m + 1)) ℤ) (G : MvPolynomial (Fin (n + 1)) ℤ)
    (μ : Mass (Fin (m + 1) → ℕ)) (ν : Mass (Fin (n + 1) → ℕ))
    (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ x, 0 ≤ ν x) :
    event (tensor μ ν) (commonPrimeEvent w F G) ≤
      event (tensor μ ν) (fun xy => MvPolynomial.eval (fun i => (Fin.tail xy.1 i : ℤ))
        (integerPolynomialMainLeading F) = 0) +
      (event (tensor μ ν) (fun xy => MvPolynomial.eval (fun i => (Fin.tail xy.2 i : ℤ))
        (integerPolynomialMainLeading G) = 0) +
      (event (tensor μ ν) (fun xy => commonPrimeEvent w (integerPolynomialMainLeading F) G
        (Fin.tail xy.1, xy.2)) +
      (event (tensor μ ν) (fun xy => commonPrimeEvent w F (integerPolynomialMainLeading G)
        (xy.1, Fin.tail xy.2)) + event (tensor μ ν) (regularCommonPrimeEvent w F G)))) := by
  let ZA := fun xy : (Fin (m + 1) → ℕ) × (Fin (n + 1) → ℕ) =>
    MvPolynomial.eval (fun i => (Fin.tail xy.1 i : ℤ)) (integerPolynomialMainLeading F) = 0
  let ZB := fun xy : (Fin (m + 1) → ℕ) × (Fin (n + 1) → ℕ) =>
    MvPolynomial.eval (fun i => (Fin.tail xy.2 i : ℤ)) (integerPolynomialMainLeading G) = 0
  let EA := fun xy : (Fin (m + 1) → ℕ) × (Fin (n + 1) → ℕ) =>
    commonPrimeEvent w (integerPolynomialMainLeading F) G (Fin.tail xy.1, xy.2)
  let EB := fun xy : (Fin (m + 1) → ℕ) × (Fin (n + 1) → ℕ) =>
    commonPrimeEvent w F (integerPolynomialMainLeading G) (xy.1, Fin.tail xy.2)
  let ER := regularCommonPrimeEvent w F G
  have hnn := tensor_nonneg μ ν hμ hν
  have hm := event_mono (tensor μ ν) hnn (E := commonPrimeEvent w F G)
    (F := fun xy => ZA xy ∨ ZB xy ∨ EA xy ∨ EB xy ∨ ER xy)
    (fun xy h => commonPrimeEvent_leading_decomposition F G xy h)
  have h1 := event_or_le (tensor μ ν) ZA (fun x => ZB x ∨ EA x ∨ EB x ∨ ER x) hnn
  have h2 := event_or_le (tensor μ ν) ZB (fun x => EA x ∨ EB x ∨ ER x) hnn
  have h3 := event_or_le (tensor μ ν) EA (fun x => EB x ∨ ER x) hnn
  have h4 := event_or_le (tensor μ ν) EB ER hnn
  linarith

end Hindman168
