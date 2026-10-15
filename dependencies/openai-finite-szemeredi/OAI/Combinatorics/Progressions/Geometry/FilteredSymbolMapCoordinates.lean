/- Modified 2026-10-15 for Lean 4.32.2 / mathlib 905b958: compatibility-only lemma renaming. Source: openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a, Apache-2.0. -/
import OAI.Combinatorics.Progressions.Polynomial.RealAdaptedPolynomialGroup

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (f : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (f '' {i | j ≤ ν i}))
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j) (w : σ → ℕ)

theorem filteredPolynomialSymbolMap_basis_repr [DecidableEq σ]
    (a : SymbolBasisIndex w ω) (b : SymbolBasisIndex w ν) :
    (G.polynomialSymbolBasis f ν hG w).repr
      (F.filteredPolynomialSymbolMap G φ hφ w (F.polynomialSymbolBasis e ω hF w a)) b =
      if a.val.1 = b.val.1 then f.repr (φ (e a.val.2)) b.val.2 else 0 := by
  rw [F.polynomialSymbolBasis_apply, F.filteredPolynomialSymbolMap_symbol,
    G.polynomialSymbolBasis_repr_map, F.filteredPolynomialMap_coefficient,
    F.adaptedMonomialBasis_coe, coefficients_monomial]
  by_cases hab : a.val.1 = b.val.1
  · simp only [hab, Finsupp.single_eq_same, ite_true]
  · rw [Finsupp.single_eq_of_ne (Ne.symm hab), map_zero, map_zero, Finsupp.zero_apply,
      if_neg hab]

theorem filteredPolynomialSymbolMap_monomial_blocks
    (a : SymbolBasisIndex w ω) (b : SymbolBasisIndex w ν) (hab : b.val.1 ≠ a.val.1) :
    (G.polynomialSymbolBasis f ν hG w).repr
      (F.filteredPolynomialSymbolMap G φ hφ w (F.polynomialSymbolBasis e ω hF w a)) b = 0 := by
  classical
  rw [F.filteredPolynomialSymbolMap_basis_repr G e ω hF f ν hG φ hφ w a b,
    if_neg (Ne.symm hab)]

theorem filteredPolynomialSymbolMap_basis_height {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H)
    (a : SymbolBasisIndex w ω) (b : SymbolBasisIndex w ν) :
    RationalHeightLE ((G.polynomialSymbolBasis f ν hG w).repr
      (F.filteredPolynomialSymbolMap G φ hφ w (F.polynomialSymbolBasis e ω hF w a)) b) H := by
  classical
  rw [F.filteredPolynomialSymbolMap_basis_repr G e ω hF f ν hG φ hφ w a b]
  split_ifs
  · exact hentries b.val.2 a.val.2
  · exact rationalHeightLE_zero hH

end Erdos3.NilpotentLieFiltration

end

end OAI
