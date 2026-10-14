import Hindman168.ValuationCellBounds
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Uniform moments for the actual comparison row valuations

Every finite partial sum is controlled by the valuation-cell covers.
The resulting constants are independent of the prime, coprime modulus,
comparison exponents, and valuation cutoff. Nonnegative summation then
gives genuine countable expectations, rather than a conditional moment
assumption or a finite-support substitute.
-/

namespace Hindman168

open scoped BigOperators Classical

theorem finite_localExcessBeta_bad_weight_bound (p b q : ℕ) [NeZero p]
    (hp : 2 ≤ p) (T : Finset (Fin q → ℕ)) :
    (∑ a ∈ T, rowValuationWeight p b a * localExcessBeta p a True) ≤
      polynomialGeometricConstant ((b + 1) * q) / (p : ℝ) := by
  classical
  let H := T.sup rowMaxValuation
  have hc : ∀ a ∈ T, rowValuationWeight p b a * localExcessBeta p a True ≠ 0 →
      ∃ n ∈ Finset.range H, a ∈ maxValuationCell q (n + 1) := by
    intro a ha hn
    have htwo : 2 ≤ (positiveRowSet a).card := by
      by_contra h
      have hz := localExcessBeta_eq_zero_of_few (p := p) a True (by omega)
      rw [hz, mul_zero] at hn
      exact hn rfl
    obtain ⟨u, v, _, hv, hm, _, _⟩ := exists_top_two_rows a htwo
    have hpos : 0 < rowMaxValuation a := hv.trans_le (rowValuation_le_max a v)
    have hH : rowMaxValuation a ≤ H := Finset.le_sup (f := rowMaxValuation) ha
    refine ⟨rowMaxValuation a - 1, Finset.mem_range.mpr (by omega), ?_⟩
    apply (mem_maxValuationCell a).mpr
    constructor
    · intro i
      have hi := rowValuation_le_max a i
      omega
    · omega
  calc
    _ ≤ ∑ n ∈ Finset.range H, ∑ a ∈ maxValuationCell q (n + 1),
        rowValuationWeight p b a * localExcessBeta p a True :=
      finite_nonnegative_sum_le_cover T (Finset.range H) (fun n => maxValuationCell q (n + 1))
        _ (fun a => mul_nonneg (rowValuationWeight_nonneg p b a) (localExcessBeta_nonneg p a True)) hc
    _ ≤ ∑ n ∈ Finset.range H,
        ((n + 2 : ℕ) : ℝ) ^ ((b + 1) * q) * ((p : ℝ) ^ (n + 1))⁻¹ := by
      apply Finset.sum_le_sum
      intro n _
      simpa only [Nat.add_assoc] using maxValuationCell_bad_sum_le p b q (n + 1)
    _ ≤ _ := finite_polynomial_geometric_bound ((b + 1) * q) p hp _

theorem finite_localExcessBeta_good_weight_bound (p b q : ℕ) [NeZero p]
    (hp : 2 ≤ p) (T : Finset (Fin q → ℕ)) :
    (∑ a ∈ T, rowValuationWeight p b a * localExcessBeta p a False) ≤
      (q : ℝ) * (polynomialGeometricConstant b *
        polynomialGeometricConstant ((b + 1) * q) / (p : ℝ) ^ 2) := by
  classical
  let H := T.sup rowMaxValuation
  let S := (Finset.univ : Finset (Fin q)).product ((Finset.range H).product (Finset.range H))
  let C := fun i : Fin q × ℕ × ℕ => topValuationCell i.1 (i.2.1 + 1) (i.2.2 + 1)
  have hc : ∀ a ∈ T, rowValuationWeight p b a * localExcessBeta p a False ≠ 0 →
      ∃ i ∈ S, a ∈ C i := by
    intro a ha hn
    have htwo : 2 ≤ (positiveRowSet a).card := by
      by_contra h
      have hz := localExcessBeta_eq_zero_of_few (p := p) a False (by omega)
      rw [hz, mul_zero] at hn
      exact hn rfl
    obtain ⟨u, v, _, hv, hm, ht, ho⟩ := exists_top_two_rows a htwo
    have hu : 0 < a u := by
      have hi := rowValuation_le_max a v
      omega
    have hH : rowMaxValuation a ≤ H := Finset.le_sup (f := rowMaxValuation) ha
    have hvH : a v ≤ H := (rowValuation_le_max a v).trans hH
    refine ⟨(u, a u - 1, a v - 1), ?_, ?_⟩
    · apply Finset.mem_product.mpr
      refine ⟨Finset.mem_univ u, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
      · apply Finset.mem_range.mpr
        change a u - 1 < H
        omega
      · apply Finset.mem_range.mpr
        change a v - 1 < H
        omega
    · change a ∈ topValuationCell u (a u - 1 + 1) (a v - 1 + 1)
      apply (mem_topValuationCell u a).mpr
      refine ⟨by omega, ?_, by omega⟩
      intro i hi
      have hh := ho i hi
      omega
  calc
    _ ≤ ∑ i ∈ S, ∑ a ∈ C i,
        rowValuationWeight p b a * localExcessBeta p a False :=
      finite_nonnegative_sum_le_cover T S C _
        (fun a => mul_nonneg (rowValuationWeight_nonneg p b a) (localExcessBeta_nonneg p a False)) hc
    _ = ∑ u : Fin q, ∑ n ∈ Finset.range H, ∑ m ∈ Finset.range H,
        ∑ a ∈ topValuationCell u (n + 1) (m + 1),
          rowValuationWeight p b a * localExcessBeta p a False := by
      dsimp only [S, C]
      simp only [Finset.product_eq_sprod, Finset.sum_product]
    _ ≤ ∑ _u : Fin q, ∑ n ∈ Finset.range H, ∑ m ∈ Finset.range H,
        (((n + 2 : ℕ) : ℝ) ^ b * ((m + 2 : ℕ) : ℝ) ^ ((b + 1) * q)) *
          ((p : ℝ) ^ (n + m + 2))⁻¹ := by
      apply Finset.sum_le_sum
      intro u _
      apply Finset.sum_le_sum
      intro n _
      apply Finset.sum_le_sum
      intro m _
      have he : n + 1 + (m + 1) = n + m + 2 := by omega
      simpa only [Nat.add_assoc, he] using topValuationCell_good_sum_le p b (n + 1) (m + 1) u
    _ ≤ ∑ _u : Fin q, polynomialGeometricConstant b *
        polynomialGeometricConstant ((b + 1) * q) / (p : ℝ) ^ 2 :=
      Finset.sum_le_sum (fun _ _ => finite_polynomial_geometric_pair_bound b ((b + 1) * q) p hp _ _)
    _ = _ := by simp

theorem comparisonRowPMF_bad_beta_finite_bound {q : ℕ} {κ : Type*} [Fintype κ]
    (s : Fin q → κ → ℝ) (hs : ∀ i j, 1 < s i j) (W p : ℕ)
    (hp : p.Prime) (hc : p.Coprime W) (T : Finset (Fin q → ℕ)) :
    (∑ a ∈ T, (((comparisonRowPMF s hs W).map
        (fun x i => (x i).factorization p)) a).toReal * localExcessBeta p a True) ≤
      polynomialGeometricConstant ((Fintype.card κ + 1) * q) / (p : ℝ) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  exact (Finset.sum_le_sum (fun a _ => comparisonRowPMF_beta_atom_le s hs W p hp hc a True)).trans
    (finite_localExcessBeta_bad_weight_bound p (Fintype.card κ) q hp.two_le T)

theorem comparisonRowPMF_good_beta_finite_bound {q : ℕ} {κ : Type*} [Fintype κ]
    (s : Fin q → κ → ℝ) (hs : ∀ i j, 1 < s i j) (W p : ℕ)
    (hp : p.Prime) (hc : p.Coprime W) (T : Finset (Fin q → ℕ)) :
    (∑ a ∈ T, (((comparisonRowPMF s hs W).map
        (fun x i => (x i).factorization p)) a).toReal * localExcessBeta p a False) ≤
      (q : ℝ) * (polynomialGeometricConstant (Fintype.card κ) *
        polynomialGeometricConstant ((Fintype.card κ + 1) * q) / (p : ℝ) ^ 2) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  exact (Finset.sum_le_sum (fun a _ => comparisonRowPMF_beta_atom_le s hs W p hp hc a False)).trans
    (finite_localExcessBeta_good_weight_bound p (Fintype.card κ) q hp.two_le T)

theorem comparisonRowPMF_bad_beta_summable {q : ℕ} {κ : Type*} [Fintype κ]
    (s : Fin q → κ → ℝ) (hs : ∀ i j, 1 < s i j) (W p : ℕ)
    (hp : p.Prime) (hc : p.Coprime W) :
    Summable (fun a => (((comparisonRowPMF s hs W).map
      (fun x i => (x i).factorization p)) a).toReal * localExcessBeta p a True) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  exact summable_of_sum_le
    (fun a => mul_nonneg ENNReal.toReal_nonneg (localExcessBeta_nonneg p a True))
    (comparisonRowPMF_bad_beta_finite_bound s hs W p hp hc)

theorem comparisonRowPMF_good_beta_summable {q : ℕ} {κ : Type*} [Fintype κ]
    (s : Fin q → κ → ℝ) (hs : ∀ i j, 1 < s i j) (W p : ℕ)
    (hp : p.Prime) (hc : p.Coprime W) :
    Summable (fun a => (((comparisonRowPMF s hs W).map
      (fun x i => (x i).factorization p)) a).toReal * localExcessBeta p a False) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  exact summable_of_sum_le
    (fun a => mul_nonneg ENNReal.toReal_nonneg (localExcessBeta_nonneg p a False))
    (comparisonRowPMF_good_beta_finite_bound s hs W p hp hc)

theorem comparisonRowPMF_bad_beta_tsum_bound {q : ℕ} {κ : Type*} [Fintype κ]
    (s : Fin q → κ → ℝ) (hs : ∀ i j, 1 < s i j) (W p : ℕ)
    (hp : p.Prime) (hc : p.Coprime W) :
    (∑' a, (((comparisonRowPMF s hs W).map
      (fun x i => (x i).factorization p)) a).toReal * localExcessBeta p a True) ≤
      polynomialGeometricConstant ((Fintype.card κ + 1) * q) / (p : ℝ) :=
  (comparisonRowPMF_bad_beta_summable s hs W p hp hc).tsum_le_of_sum_le
    (comparisonRowPMF_bad_beta_finite_bound s hs W p hp hc)

theorem comparisonRowPMF_good_beta_tsum_bound {q : ℕ} {κ : Type*} [Fintype κ]
    (s : Fin q → κ → ℝ) (hs : ∀ i j, 1 < s i j) (W p : ℕ)
    (hp : p.Prime) (hc : p.Coprime W) :
    (∑' a, (((comparisonRowPMF s hs W).map
      (fun x i => (x i).factorization p)) a).toReal * localExcessBeta p a False) ≤
      (q : ℝ) * (polynomialGeometricConstant (Fintype.card κ) *
        polynomialGeometricConstant ((Fintype.card κ + 1) * q) / (p : ℝ) ^ 2) :=
  (comparisonRowPMF_good_beta_summable s hs W p hp hc).tsum_le_of_sum_le
    (comparisonRowPMF_good_beta_finite_bound s hs W p hp hc)

end Hindman168
