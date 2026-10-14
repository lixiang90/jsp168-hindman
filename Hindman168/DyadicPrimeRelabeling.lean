import Hindman168.DyadicCoprimalityBase
import Hindman168.CoordinateLists
import Mathlib.Data.Finset.Max

/-!
# Exact permutation and orientation of actual dyadic prime tuples

The endpoint family and polynomial variables are permuted together.
The original weighted event mass is unchanged. A finite maximum picks
a largest endpoint, which can be placed in coordinate zero by a swap.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem unequalDyadicPrimeMass_reindex {n : ℕ} (e : Fin n → ℕ) (s : Equiv.Perm (Fin n)) :
    (unequalDyadicPrimeMass e).mapDomain (fun x i => x (s i)) =
      unequalDyadicPrimeMass (fun i => e (s i)) := piMass_reindex _ s

theorem integerPolynomial_permuted_eval {n : ℕ} (s : Equiv.Perm (Fin n))
    (F : MvPolynomial (Fin n) ℤ) (x : Fin n → ℕ) :
    MvPolynomial.eval (fun i => (x (s i) : ℤ)) (MvPolynomial.rename s.symm F) =
      MvPolynomial.eval (fun i => (x i : ℤ)) F := by
  rw [MvPolynomial.eval_rename]
  simp only [Function.comp_def, Equiv.apply_symm_apply]

theorem integerPolynomial_permuted_ne_zero {n : ℕ} (s : Equiv.Perm (Fin n))
    {F : MvPolynomial (Fin n) ℤ} (hF : F ≠ 0) : MvPolynomial.rename s.symm F ≠ 0 := by
  intro h
  apply hF
  apply MvPolynomial.rename_injective s.symm s.symm.injective
  simpa only [map_zero] using h

theorem dyadic_commonPrimeEvent_reindex {m n w : ℕ}
    (eF : Fin m → ℕ) (eG : Fin n → ℕ)
    (s : Equiv.Perm (Fin m)) (t : Equiv.Perm (Fin n))
    (F : MvPolynomial (Fin m) ℤ) (G : MvPolynomial (Fin n) ℤ) :
    event (tensor (unequalDyadicPrimeMass (fun i => eF (s i)))
      (unequalDyadicPrimeMass (fun i => eG (t i))))
      (commonPrimeEvent w (MvPolynomial.rename s.symm F) (MvPolynomial.rename t.symm G)) =
      event (tensor (unequalDyadicPrimeMass eF) (unequalDyadicPrimeMass eG))
        (commonPrimeEvent w F G) := by
  have hm := tensor_map (unequalDyadicPrimeMass eF) (unequalDyadicPrimeMass eG)
    (fun x i => x (s i)) (fun x i => x (t i))
  rw [unequalDyadicPrimeMass_reindex, unequalDyadicPrimeMass_reindex] at hm
  rw [← hm, event_map]
  congr 1
  funext xy
  simp only [commonPrimeEvent, integerPolynomial_permuted_eval]

theorem dyadic_commonPrimeEvent_swap {m n w : ℕ}
    (eF : Fin m → ℕ) (eG : Fin n → ℕ)
    (F : MvPolynomial (Fin m) ℤ) (G : MvPolynomial (Fin n) ℤ) :
    event (tensor (unequalDyadicPrimeMass eG) (unequalDyadicPrimeMass eF))
      (commonPrimeEvent w G F) =
      event (tensor (unequalDyadicPrimeMass eF) (unequalDyadicPrimeMass eG))
        (commonPrimeEvent w F G) := by
  rw [← tensor_swap (unequalDyadicPrimeMass eF) (unequalDyadicPrimeMass eG), event_map]
  congr 1
  funext xy
  exact propext (commonPrimeEvent_swap F G xy).symm

theorem exists_largest_dyadic_main_permutation {n : ℕ} (e : Fin (n + 1) → ℕ) :
    ∃ s : Equiv.Perm (Fin (n + 1)), ∀ i, e (s i) ≤ e (s 0) := by
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ e ⟨0, Finset.mem_univ 0⟩
  refine ⟨Equiv.swap 0 j, ?_⟩
  intro i
  simpa only [Equiv.swap_apply_left] using hj (Equiv.swap 0 j i) (Finset.mem_univ _)

end Hindman168
