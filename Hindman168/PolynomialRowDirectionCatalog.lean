import Hindman168.PolynomialKernelDirectionSelection

/-!
# Actual finite response/denominator/minor catalogue

A row family carries explicit nonzero anchors and nonparallel minor evidence.
Its directions are selected from the bounded construction, not supplied as
hypotheses. The catalogue contains 1, the designated denominator, all nonzero
responses, all nonzero coefficients and all nonzero two-column minors.
-/

namespace Hindman168

open scoped BigOperators Classical

structure PolynomialRowFamily (R : Type*) [CommRing R] (r m : ℕ) where
  row : Fin r → Fin (m + 1) → R
  anchor : Fin r → Fin (m + 1)
  anchor_ne_zero : ∀ i, row i (anchor i) ≠ 0
  pair_minor : ∀ i l, l ≠ i → ∃ k c, polynomialRowMinor (row i) (row l) k c ≠ 0

namespace PolynomialRowFamily

variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R] {r m : ℕ}

noncomputable def direction (F : PolynomialRowFamily R r m) (i : Fin r) : Fin (m + 1) → R :=
  selectedKernelDirection F.row F.anchor F.anchor_ne_zero F.pair_minor i

noncomputable def response (F : PolynomialRowFamily R r m) (l i : Fin r) : R :=
  polynomialRowResponse (F.row l) (F.direction i)

theorem response_self (F : PolynomialRowFamily R r m) (i : Fin r) : F.response i i = 0 :=
  selectedKernelDirection_annihilates _ _ _ _ i

theorem response_ne_zero (F : PolynomialRowFamily R r m) (l i : Fin r) (hi : l ≠ i) :
    F.response l i ≠ 0 :=
  selectedKernelDirection_response_ne_zero _ _ _ _ i l hi

noncomputable def denominator (F : PolynomialRowFamily R r m) (target : Fin r) : R :=
  ∏ i ∈ Finset.univ.erase target, F.response target i

theorem denominator_ne_zero (F : PolynomialRowFamily R r m) (target : Fin r) :
    F.denominator target ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact F.response_ne_zero target i (Finset.mem_erase.mp hi).1.symm

noncomputable def rawCatalog (F : PolynomialRowFamily R r m) (target : Fin r) : Finset R :=
  {1, F.denominator target} ∪
    Finset.univ.image (fun p : Fin r × Fin r => F.response p.1 p.2) ∪
    Finset.univ.image (fun p : Fin r × Fin (m + 1) => F.row p.1 p.2) ∪
    Finset.univ.image (fun p : (Fin r × Fin r) × (Fin (m + 1) × Fin (m + 1)) =>
      polynomialRowMinor (F.row p.1.1) (F.row p.1.2) p.2.1 p.2.2)

noncomputable def catalog (F : PolynomialRowFamily R r m) (target : Fin r) : Finset R :=
  (F.rawCatalog target).filter (fun f => f ≠ 0)

theorem catalog_nonzero (F : PolynomialRowFamily R r m) (target : Fin r) :
    ∀ f ∈ F.catalog target, f ≠ 0 := by
  intro f hf
  exact (Finset.mem_filter.mp hf).2

theorem one_mem_catalog (F : PolynomialRowFamily R r m) (target : Fin r) :
    1 ∈ F.catalog target := by
  simp [catalog, rawCatalog]

theorem denominator_mem_catalog (F : PolynomialRowFamily R r m) (target : Fin r) :
    F.denominator target ∈ F.catalog target := by
  exact Finset.mem_filter.mpr ⟨by simp [rawCatalog], F.denominator_ne_zero target⟩

theorem response_mem_catalog (F : PolynomialRowFamily R r m) (target l i : Fin r)
    (hi : l ≠ i) : F.response l i ∈ F.catalog target := by
  refine Finset.mem_filter.mpr ⟨?_, F.response_ne_zero l i hi⟩
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨(l, i), Finset.mem_univ _, rfl⟩

theorem coefficient_mem_catalog (F : PolynomialRowFamily R r m) (target i : Fin r)
    (k : Fin (m + 1)) (hk : F.row i k ≠ 0) : F.row i k ∈ F.catalog target := by
  refine Finset.mem_filter.mpr ⟨?_, hk⟩
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨(i, k), Finset.mem_univ _, rfl⟩

theorem minor_mem_catalog (F : PolynomialRowFamily R r m) (target i l : Fin r)
    (k c : Fin (m + 1)) (h : polynomialRowMinor (F.row i) (F.row l) k c ≠ 0) :
    polynomialRowMinor (F.row i) (F.row l) k c ∈ F.catalog target := by
  refine Finset.mem_filter.mpr ⟨?_, h⟩
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨((i, l), (k, c)), Finset.mem_univ _, rfl⟩

theorem anchor_mem_catalog (F : PolynomialRowFamily R r m) (target i : Fin r) :
    F.row i (F.anchor i) ∈ F.catalog target :=
  F.coefficient_mem_catalog target i (F.anchor i) (F.anchor_ne_zero i)

end PolynomialRowFamily
end Hindman168
