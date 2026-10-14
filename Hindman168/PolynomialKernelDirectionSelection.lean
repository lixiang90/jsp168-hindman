import Hindman168.PolynomialKernelCurve

/-!
# Bounded simultaneous direction selection for a finite row family

The product of the off-diagonal response polynomials is nonzero and has
bounded degree. Testing the first B+1 positive integers therefore supplies
an actual polynomial direction, before any prime specialization.
-/

namespace Hindman168

open scoped BigOperators Classical

noncomputable def kernelOtherResponseProduct {R : Type*} [CommRing R] {m r : ℕ}
    (A : Fin r → Fin (m + 1) → R) (i : Fin r) (j : Fin (m + 1)) : Polynomial R :=
  ∏ l ∈ Finset.univ.erase i, kernelResponsePolynomial (A i) (A l) j

theorem kernelOtherResponseProduct_ne_zero {R : Type*}
    [CommRing R] [IsDomain R] {m r : ℕ}
    (A : Fin r → Fin (m + 1) → R) (i : Fin r) (j : Fin (m + 1))
    (hj : A i j ≠ 0)
    (hp : ∀ l, l ≠ i → ∃ k c, polynomialRowMinor (A i) (A l) k c ≠ 0) :
    kernelOtherResponseProduct A i j ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro l hl
  exact kernelResponsePolynomial_ne_zero (A i) (A l) j hj
    (hp l (Finset.mem_erase.mp hl).1)

theorem kernelOtherResponseProduct_natDegree_le {R : Type*} [CommRing R] {m r : ℕ}
    (A : Fin r → Fin (m + 1) → R) (i : Fin r) (j : Fin (m + 1)) :
    (kernelOtherResponseProduct A i j).natDegree ≤ (r - 1) * (m - 1) := by
  calc
    _ ≤ ∑ l ∈ Finset.univ.erase i, (kernelResponsePolynomial (A i) (A l) j).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _l ∈ Finset.univ.erase i, (m - 1) :=
      Finset.sum_le_sum (fun l _ => kernelResponsePolynomial_natDegree_le (A i) (A l) j)
    _ = _ := by simp

theorem exists_bounded_polynomial_kernel_parameter {R : Type*}
    [CommRing R] [IsDomain R] [CharZero R] {m r : ℕ}
    (A : Fin r → Fin (m + 1) → R) (i : Fin r) (j : Fin (m + 1))
    (hj : A i j ≠ 0)
    (hp : ∀ l, l ≠ i → ∃ k c, polynomialRowMinor (A i) (A l) k c ≠ 0) :
    ∃ t : ℕ, 1 ≤ t ∧ t ≤ (r - 1) * (m - 1) + 1 ∧
      polynomialRowResponse (A i) (polynomialKernelCurve (A i) j t) = 0 ∧
      ∀ l, l ≠ i → polynomialRowResponse (A l) (polynomialKernelCurve (A i) j t) ≠ 0 := by
  obtain ⟨t, ht, hB, hP⟩ := polynomial_exists_positive_bounded_eval_ne_zero
    (kernelOtherResponseProduct A i j) (kernelOtherResponseProduct_ne_zero A i j hj hp)
    ((r - 1) * (m - 1)) (kernelOtherResponseProduct_natDegree_le A i j)
  refine ⟨t, ht, hB, polynomialKernelCurve_annihilates _ _ _, ?_⟩
  have hprod : (∏ l ∈ Finset.univ.erase i,
      (kernelResponsePolynomial (A i) (A l) j).eval (t : R)) ≠ 0 := by
    simpa only [kernelOtherResponseProduct, Polynomial.eval_prod] using hP
  intro l hl
  rw [polynomialKernelCurve_response]
  exact Finset.prod_ne_zero_iff.mp hprod l (Finset.mem_erase.mpr ⟨hl, Finset.mem_univ _⟩)

noncomputable def selectedKernelParameter {R : Type*}
    [CommRing R] [IsDomain R] [CharZero R] {m r : ℕ}
    (A : Fin r → Fin (m + 1) → R) (anchor : Fin r → Fin (m + 1))
    (ha : ∀ i, A i (anchor i) ≠ 0)
    (hp : ∀ i l, l ≠ i → ∃ k c, polynomialRowMinor (A i) (A l) k c ≠ 0)
    (i : Fin r) : ℕ :=
  Classical.choose (exists_bounded_polynomial_kernel_parameter A i (anchor i) (ha i) (hp i))

noncomputable def selectedKernelDirection {R : Type*}
    [CommRing R] [IsDomain R] [CharZero R] {m r : ℕ}
    (A : Fin r → Fin (m + 1) → R) (anchor : Fin r → Fin (m + 1))
    (ha : ∀ i, A i (anchor i) ≠ 0)
    (hp : ∀ i l, l ≠ i → ∃ k c, polynomialRowMinor (A i) (A l) k c ≠ 0)
    (i : Fin r) : Fin (m + 1) → R :=
  polynomialKernelCurve (A i) (anchor i) (selectedKernelParameter A anchor ha hp i)

theorem selectedKernelParameter_bounds {R : Type*}
    [CommRing R] [IsDomain R] [CharZero R] {m r : ℕ}
    (A : Fin r → Fin (m + 1) → R) (anchor : Fin r → Fin (m + 1))
    (ha : ∀ i, A i (anchor i) ≠ 0)
    (hp : ∀ i l, l ≠ i → ∃ k c, polynomialRowMinor (A i) (A l) k c ≠ 0)
    (i : Fin r) : 1 ≤ selectedKernelParameter A anchor ha hp i ∧
      selectedKernelParameter A anchor ha hp i ≤ (r - 1) * (m - 1) + 1 := by
  have h := Classical.choose_spec
    (exists_bounded_polynomial_kernel_parameter A i (anchor i) (ha i) (hp i))
  exact ⟨h.1, h.2.1⟩

theorem selectedKernelDirection_annihilates {R : Type*}
    [CommRing R] [IsDomain R] [CharZero R] {m r : ℕ}
    (A : Fin r → Fin (m + 1) → R) (anchor : Fin r → Fin (m + 1))
    (ha : ∀ i, A i (anchor i) ≠ 0)
    (hp : ∀ i l, l ≠ i → ∃ k c, polynomialRowMinor (A i) (A l) k c ≠ 0)
    (i : Fin r) : polynomialRowResponse (A i) (selectedKernelDirection A anchor ha hp i) = 0 :=
  polynomialKernelCurve_annihilates _ _ _

theorem selectedKernelDirection_response_ne_zero {R : Type*}
    [CommRing R] [IsDomain R] [CharZero R] {m r : ℕ}
    (A : Fin r → Fin (m + 1) → R) (anchor : Fin r → Fin (m + 1))
    (ha : ∀ i, A i (anchor i) ≠ 0)
    (hp : ∀ i l, l ≠ i → ∃ k c, polynomialRowMinor (A i) (A l) k c ≠ 0)
    (i l : Fin r) (hl : l ≠ i) :
    polynomialRowResponse (A l) (selectedKernelDirection A anchor ha hp i) ≠ 0 := by
  exact (Classical.choose_spec
    (exists_bounded_polynomial_kernel_parameter A i (anchor i) (ha i) (hp i))).2.2.2 l hl

end Hindman168
