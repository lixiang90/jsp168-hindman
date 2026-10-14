import Hindman168.IndependentRowMinors
import Mathlib.Algebra.Polynomial.Roots

/-!
# Explicit polynomial kernel basis and nonzero row responses

The basis is the one used in the correlation proof: A_j e_k-A_k e_j.
A nonzero two-column minor gives a nonzero response at any chosen nonzero
anchor of A, using only domain cancellation and polynomial identities.
-/

namespace Hindman168

open scoped BigOperators Classical

noncomputable def polynomialRowResponse {R : Type*} [CommRing R] {m : ℕ}
    (A v : Fin m → R) : R := ∑ k, A k * v k

noncomputable def polynomialRowMinor {R : Type*} [CommRing R] {m : ℕ}
    (A B : Fin m → R) (j k : Fin m) : R := A j * B k - A k * B j

noncomputable def polynomialKernelBasis {R : Type*} [CommRing R] {m : ℕ}
    (A : Fin m → R) (j k : Fin m) : Fin m → R :=
  fun c => A j * (if c = k then 1 else 0) - A k * (if c = j then 1 else 0)

theorem polynomialKernelBasis_response {R : Type*} [CommRing R] {m : ℕ}
    (A B : Fin m → R) (j k : Fin m) :
    polynomialRowResponse B (polynomialKernelBasis A j k) = polynomialRowMinor A B j k := by
  simp only [polynomialRowResponse, polynomialKernelBasis, mul_sub, mul_ite,
    mul_one, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  unfold polynomialRowMinor
  ring

theorem polynomialKernelBasis_annihilates {R : Type*} [CommRing R] {m : ℕ}
    (A : Fin m → R) (j k : Fin m) :
    polynomialRowResponse A (polynomialKernelBasis A j k) = 0 := by
  rw [polynomialKernelBasis_response]
  unfold polynomialRowMinor
  ring

theorem polynomialRowMinor_anchor_exists {R : Type*} [CommRing R] [IsDomain R] {m : ℕ}
    (A B : Fin m → R) (j : Fin m) (hj : A j ≠ 0)
    (hpair : ∃ k l, polynomialRowMinor A B k l ≠ 0) :
    ∃ k, polynomialRowMinor A B j k ≠ 0 := by
  by_contra! hz
  obtain ⟨k, l, hkl⟩ := hpair
  have hid : A j * polynomialRowMinor A B k l =
      A k * polynomialRowMinor A B j l - A l * polynomialRowMinor A B j k := by
    unfold polynomialRowMinor
    ring
  have hh : A j * polynomialRowMinor A B k l = 0 := by
    rw [hid, hz l, hz k, mul_zero, mul_zero, sub_self]
  exact hkl ((mul_eq_zero.mp hh).resolve_left hj)

theorem polynomialRowMinor_off_anchor_exists {R : Type*} [CommRing R] [IsDomain R] {m : ℕ}
    (A B : Fin (m + 1) → R) (j : Fin (m + 1)) (hj : A j ≠ 0)
    (hpair : ∃ k l, polynomialRowMinor A B k l ≠ 0) :
    ∃ k : Fin m, polynomialRowMinor A B j (j.succAbove k) ≠ 0 := by
  obtain ⟨k, hk⟩ := polynomialRowMinor_anchor_exists A B j hj hpair
  have hkj : k ≠ j := by
    rintro rfl
    exact hk (by unfold polynomialRowMinor; ring)
  obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hkj
  exact ⟨a, ha ▸ hk⟩

end Hindman168
