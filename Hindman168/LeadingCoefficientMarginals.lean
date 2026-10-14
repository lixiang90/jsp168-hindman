import Hindman168.LeadingCoefficientDecomposition

/-!
# Actual marginal laws in the leading-coefficient recursion

Discarding the main variable preserves the original tail law exactly.
The two recursive exceptional events therefore use genuinely independent
tuples of one fewer variable. No reweighting or new independence input
is imposed on those lower-dimensional polynomial pairs.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

theorem event_tensor_first {α β : Type*} (μ : Mass α) (ν : Mass β)
    (ht : total ν = 1) (E : α → Prop) :
    event (tensor μ ν) (fun xy => E xy.1) = event μ E := by
  rw [event_tensor]
  change (∑ b ∈ ν.support, ν b * event μ E) = event μ E
  rw [← Finset.sum_mul, ← total_eq_sum ν (Finset.Subset.refl _), ht, one_mul]

theorem event_tensor_second {α β : Type*} (μ : Mass α) (ν : Mass β)
    (ht : total μ = 1) (E : β → Prop) :
    event (tensor μ ν) (fun xy => E xy.2) = event ν E := by
  rw [event_tensor_left]
  change (∑ a ∈ μ.support, μ a * event ν E) = event ν E
  rw [← Finset.sum_mul, ← total_eq_sum μ (Finset.Subset.refl _), ht, one_mul]

end Hindman168.FiniteMass

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem unequalDyadicPrimeMass_tail {n : ℕ} (e : Fin (n + 1) → ℕ)
    (hH : ∀ i, 0 < primePoolHarmonicMass (2 ^ e i) (2 ^ (e i + 1))) :
    (unequalDyadicPrimeMass e).mapDomain (Fin.tail (α := fun _ => ℕ)) =
      unequalDyadicPrimeMass (fun i => e i.succ) :=
  piMass_restrict _ Fin.succ (Fin.succ_injective n) (fun i => primePoolMass_total (hH i))

theorem dyadic_leading_left_recursive_event {m n w : ℕ}
    (eF : Fin (m + 1) → ℕ) (eG : Fin n → ℕ)
    (hHF : ∀ i, 0 < primePoolHarmonicMass (2 ^ eF i) (2 ^ (eF i + 1)))
    (F : MvPolynomial (Fin (m + 1)) ℤ) (G : MvPolynomial (Fin n) ℤ) :
    event (tensor (unequalDyadicPrimeMass eF) (unequalDyadicPrimeMass eG))
      (fun xy => commonPrimeEvent w (integerPolynomialMainLeading F) G (Fin.tail xy.1, xy.2)) =
    event (tensor (unequalDyadicPrimeMass (fun i => eF i.succ)) (unequalDyadicPrimeMass eG))
      (commonPrimeEvent w (integerPolynomialMainLeading F) G) := by
  have hm := tensor_map (unequalDyadicPrimeMass eF) (unequalDyadicPrimeMass eG)
    (Fin.tail (α := fun _ => ℕ)) id
  rw [unequalDyadicPrimeMass_tail eF hHF, Finsupp.mapDomain_id] at hm
  rw [← hm, event_map]
  rfl

theorem dyadic_leading_right_recursive_event {m n w : ℕ}
    (eF : Fin m → ℕ) (eG : Fin (n + 1) → ℕ)
    (hHG : ∀ i, 0 < primePoolHarmonicMass (2 ^ eG i) (2 ^ (eG i + 1)))
    (F : MvPolynomial (Fin m) ℤ) (G : MvPolynomial (Fin (n + 1)) ℤ) :
    event (tensor (unequalDyadicPrimeMass eF) (unequalDyadicPrimeMass eG))
      (fun xy => commonPrimeEvent w F (integerPolynomialMainLeading G) (xy.1, Fin.tail xy.2)) =
    event (tensor (unequalDyadicPrimeMass eF) (unequalDyadicPrimeMass (fun i => eG i.succ)))
      (commonPrimeEvent w F (integerPolynomialMainLeading G)) := by
  have hm := tensor_map (unequalDyadicPrimeMass eF) (unequalDyadicPrimeMass eG)
    id (Fin.tail (α := fun _ => ℕ))
  rw [Finsupp.mapDomain_id, unequalDyadicPrimeMass_tail eG hHG] at hm
  rw [← hm, event_map]
  rfl

theorem dyadic_leading_zero_left_event {m n : ℕ}
    (eF : Fin (m + 1) → ℕ) (eG : Fin n → ℕ)
    (hHF : ∀ i, 0 < primePoolHarmonicMass (2 ^ eF i) (2 ^ (eF i + 1)))
    (hHG : ∀ i, 0 < primePoolHarmonicMass (2 ^ eG i) (2 ^ (eG i + 1)))
    (F : MvPolynomial (Fin (m + 1)) ℤ) :
    event (tensor (unequalDyadicPrimeMass eF) (unequalDyadicPrimeMass eG))
      (fun xy => MvPolynomial.eval (fun i => (Fin.tail xy.1 i : ℤ)) (integerPolynomialMainLeading F) = 0) =
    event (unequalDyadicPrimeMass (fun i => eF i.succ))
      (fun x => MvPolynomial.eval (fun i => (x i : ℤ)) (integerPolynomialMainLeading F) = 0) := by
  rw [event_tensor_first (unequalDyadicPrimeMass eF) (unequalDyadicPrimeMass eG)
    (unequalDyadicPrimeMass_total eG hHG)
    (fun x : Fin (m + 1) → ℕ => MvPolynomial.eval (fun i => (Fin.tail x i : ℤ))
      (integerPolynomialMainLeading F) = 0)]
  rw [← unequalDyadicPrimeMass_tail eF hHF, event_map]

theorem dyadic_leading_zero_right_event {m n : ℕ}
    (eF : Fin m → ℕ) (eG : Fin (n + 1) → ℕ)
    (hHF : ∀ i, 0 < primePoolHarmonicMass (2 ^ eF i) (2 ^ (eF i + 1)))
    (hHG : ∀ i, 0 < primePoolHarmonicMass (2 ^ eG i) (2 ^ (eG i + 1)))
    (G : MvPolynomial (Fin (n + 1)) ℤ) :
    event (tensor (unequalDyadicPrimeMass eF) (unequalDyadicPrimeMass eG))
      (fun xy => MvPolynomial.eval (fun i => (Fin.tail xy.2 i : ℤ)) (integerPolynomialMainLeading G) = 0) =
    event (unequalDyadicPrimeMass (fun i => eG i.succ))
      (fun x => MvPolynomial.eval (fun i => (x i : ℤ)) (integerPolynomialMainLeading G) = 0) := by
  rw [event_tensor_second (unequalDyadicPrimeMass eF) (unequalDyadicPrimeMass eG)
    (unequalDyadicPrimeMass_total eF hHF)
    (fun x : Fin (n + 1) → ℕ => MvPolynomial.eval (fun i => (Fin.tail x i : ℤ))
      (integerPolynomialMainLeading G) = 0)]
  rw [← unequalDyadicPrimeMass_tail eG hHG, event_map]

end Hindman168
