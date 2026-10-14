import Hindman168.LeibmanMonomialVectors
import Mathlib.LinearAlgebra.Basis.VectorSpace

namespace Hindman168
open MvPolynomial
open scoped BigOperators Classical

theorem leibman_dense_monomial_span {K : Type*} [Field K] {n : ℕ}
    (I : Finset (Fin n → ℕ)) (d : ℕ) (hd : ∀ i ∈ I, (∑ j, i j) ≤ d)
    (S : Finset K) (hS : S.Nonempty) (T : Finset (Fin n → K))
    (hT : T ⊆ Fintype.piFinset (fun _ : Fin n => S))
    (hdense : d*S.card^n < T.card*S.card) :
    Submodule.span K (leibmanMonomialVector I '' (T : Set (Fin n → K))) = ⊤ := by
  by_contra hs
  obtain ⟨f, hf, hker⟩ := (Submodule.span K
    (leibmanMonomialVector I '' (T : Set (Fin n → K)))).exists_le_ker_of_lt_top
      (lt_top_iff_ne_top.mpr hs)
  let c : ↥I → K := fun i => f (Pi.single i 1)
  have hp : leibmanMonomialPolynomial I c ≠ 0 := leibman_monomial_polynomial_ne_zero I c
    (leibman_monomial_functional_coefficients_ne_zero I f hf)
  have hz : ∀ x ∈ T, eval x (leibmanMonomialPolynomial I c) = 0 := by
    intro x hx
    rw [leibman_monomial_vector_functional]
    exact hker (Submodule.subset_span ⟨x, hx, rfl⟩)
  exact hp (leibman_polynomial_eq_zero_of_dense_zeros _ d
    (leibman_monomial_polynomial_totalDegree I c d hd) S hS T hT hdense hz)

theorem leibman_dense_integer_directions_span {n : ℕ}
    (I : Finset (Fin n → ℕ)) (d : ℕ) (hd : ∀ i ∈ I, (∑ j, i j) ≤ d)
    (L : ℕ) (hL : 0 < L) (T : Finset (Fin n → ℕ))
    (hT : T ⊆ Fintype.piFinset (fun _ : Fin n => Finset.range L))
    (hdense : d*L^n < T.card*L) :
    Submodule.span ℚ ((fun x : Fin n → ℕ => leibmanMonomialVector I (fun j => (x j : ℚ))) ''
      (T : Set (Fin n → ℕ))) = ⊤ := by
  let S : Finset ℚ := (Finset.range L).image (fun x : ℕ => (x : ℚ))
  let e : (Fin n → ℕ) → (Fin n → ℚ) := fun x j => (x j : ℚ)
  have hcast : Function.Injective (fun x : ℕ => (x : ℚ)) := by
    intro a b h
    change (a : ℚ) = (b : ℚ) at h
    exact_mod_cast h
  have he : Function.Injective e := by
    intro x y h
    funext j
    exact hcast (congrFun h j)
  have hcard : S.card = L := by
    rw [Finset.card_image_of_injective _ hcast, Finset.card_range]
  have hS : S.Nonempty := (Finset.nonempty_range_iff.mpr hL.ne').image _
  have hQT : T.image e ⊆ Fintype.piFinset (fun _ : Fin n => S) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    apply Fintype.mem_piFinset.mpr
    intro j
    exact Finset.mem_image.mpr ⟨x j, Fintype.mem_piFinset.mp (hT hx) j, rfl⟩
  have h := leibman_dense_monomial_span I d hd S hS (T.image e) hQT
    (by simpa only [hcard, Finset.card_image_of_injective T he] using hdense)
  simpa only [Finset.coe_image, Set.image_image, Function.comp_def, e] using h

end Hindman168
