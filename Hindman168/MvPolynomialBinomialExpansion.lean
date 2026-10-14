import Hindman168.MvBinomialMonomialExpansion
import Hindman168.TorusPolynomialCharacterProjection

namespace Hindman168
open MvPolynomial
open scoped BigOperators Classical

theorem mv_polynomial_fixed_monomial_box {κ : Type*} [Fintype κ]
    (p : MvPolynomial κ ℝ) (D : ℕ) (hp : p.totalDegree ≤ D) :
    p = ∑ J ∈ mvBinomialBox κ D, monomial (Finsupp.equivFunOnFinite.symm J)
      (coeff (Finsupp.equivFunOnFinite.symm J) p) := by
  let U := (mvBinomialBox κ D).map Finsupp.equivFunOnFinite.symm.toEmbedding
  have hsub : p.support ⊆ U := by
    intro J hJ
    have hd := (le_totalDegree hJ).trans hp
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hd
    exact Finset.mem_map.mpr ⟨Finsupp.equivFunOnFinite J,
      mv_binomial_box_mem_of_weight_le D _ hd, Finsupp.equivFunOnFinite.symm_apply_apply J⟩
  have h := Finsupp.sum_of_support_subset (AddMonoidAlgebra.coeff p) hsub
    (fun J a => monomial J a) (fun _ _ => monomial_zero)
  rw [sum_def] at h
  have he : (∑ J ∈ U, monomial J (coeff J p)) = p := h.symm.trans (support_sum_monomial_coeff p)
  simpa only [U, Finset.sum_map, Equiv.toEmbedding_apply] using he.symm

/-- ACTUAL original polynomial expansion in the ACTUAL rough-box binomial
basis. All coefficients are true INTEGER triangular combinations of the
original monomial coefficients, not an assumed change of basis. -/
theorem mv_polynomial_binomial_expansion {κ : Type*} [Fintype κ]
    (p : MvPolynomial κ ℝ) (D : ℕ) (hp : p.totalDegree ≤ D) :
    p = ∑ I ∈ mvBinomialBox κ D,
      C (mvPolynomialBinomialCoefficient p D I)*roughMvBinomialPolynomial I := by
  conv_lhs => rw [mv_polynomial_fixed_monomial_box p D hp]
  conv_lhs => simp only [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.coe_equivFunOnFinite_symm]
  conv_rhs => simp only [mvPolynomialBinomialCoefficient, map_sum, Finset.sum_mul, map_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [mv_monomial_binomial_expansion J D ((mv_binomial_box_mem D J).mp hJ), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _
  ring

theorem mv_binomial_coefficient_zero_above_degree {κ : Type*} [Fintype κ]
    (p : MvPolynomial κ ℝ) (D : ℕ) (hp : p.totalDegree ≤ D) (I : κ → ℕ)
    (hI : D < ∑ j, I j) : mvPolynomialBinomialCoefficient p D I = 0 := by
  apply Finset.sum_eq_zero
  intro J _
  by_cases hJ : (∑ j, J j) ≤ D
  · rw [mv_binomial_stirling_weight_zero_of_weight_lt I J (hJ.trans_lt hI), Nat.cast_zero, mul_zero]
  · rw [scalar_mv_coefficient_zero_above_degree p D hp J (Nat.lt_of_not_ge hJ), zero_mul]

theorem mv_binomial_character_projection_coefficient {κ σ : Type*} [Fintype κ] [Fintype σ]
    (p : κ → MvPolynomial σ ℝ) (k : κ → ℤ) (D : ℕ) (I : σ → ℕ) :
    mvPolynomialBinomialCoefficient (torusPolynomialCharacterProjection p k) D I =
      ∑ j, (k j : ℝ)*mvPolynomialBinomialCoefficient (p j) D I := by
  simp only [mvPolynomialBinomialCoefficient, torus_polynomial_character_projection_coefficient,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro J _
  ring

theorem mv_multiindex_weight_zero_iff {κ : Type*} [Fintype κ] (I : κ → ℕ) :
    (∑ j, I j)=0 ↔ I=0 := by
  constructor
  · intro h
    funext j
    have hj := Finset.single_le_sum (fun k _ => Nat.zero_le (I k)) (Finset.mem_univ j)
    change I j=0
    omega
  · intro h
    simp only [h, Pi.zero_apply, Finset.sum_const_zero]

theorem mv_binomial_basis_zero (κ : Type*) [Fintype κ] :
    roughMvBinomialPolynomial (0 : κ → ℕ) = 1 := by
  simp only [roughMvBinomialPolynomial, roughMvFallingPolynomial, Pi.zero_apply,
    Nat.factorial_zero, Nat.cast_one, inv_one, C_1, Finset.range_zero, Finset.prod_empty,
    Finset.prod_const_one, one_mul]

/-- Exact original constant-plus-positive-degree form used in the paper,
after removing ACTUAL zero coefficients above the total-degree bound. -/
theorem mv_polynomial_binomial_positive_expansion {κ : Type*} [Fintype κ]
    (p : MvPolynomial κ ℝ) (D : ℕ) (hp : p.totalDegree ≤ D) :
    p = C (mvPolynomialBinomialCoefficient p D 0)+∑ I ∈ roughSpatialDegreeIndices κ D,
      C (mvPolynomialBinomialCoefficient p D I)*roughMvBinomialPolynomial I := by
  let S := roughSpatialDegreeIndices κ D
  have hsub : insert (0 : κ → ℕ) S ⊆ mvBinomialBox κ D := by
    intro I hI
    rcases Finset.mem_insert.mp hI with hzero | hpos
    · subst I
      exact (mv_binomial_box_mem D 0).mpr (fun _ => Nat.zero_le D)
    · exact mv_binomial_box_mem_of_weight_le D I ((rough_spatial_degree_indices_mem D I).mp hpos).2
  have he : (∑ I ∈ insert (0 : κ → ℕ) S,
      C (mvPolynomialBinomialCoefficient p D I)*roughMvBinomialPolynomial I) =
      ∑ I ∈ mvBinomialBox κ D, C (mvPolynomialBinomialCoefficient p D I)*roughMvBinomialPolynomial I := by
    apply Finset.sum_subset hsub
    intro I _ hnot
    have hID : D < ∑ j, I j := by
      by_contra! hlow
      have hz : I ≠ 0 := fun h => hnot (Finset.mem_insert.mpr (Or.inl h))
      have hpos : 0 < ∑ j, I j := Nat.pos_of_ne_zero
        (fun h => hz ((mv_multiindex_weight_zero_iff I).mp h))
      exact hnot (Finset.mem_insert_of_mem ((rough_spatial_degree_indices_mem D I).mpr ⟨hpos, hlow⟩))
    rw [mv_binomial_coefficient_zero_above_degree p D hp I hID, C_0, zero_mul]
  have hz : (0 : κ → ℕ) ∉ S := by
    rw [rough_spatial_degree_indices_mem]
    simp only [Pi.zero_apply, Finset.sum_const_zero, lt_self_iff_false, false_and, not_false_eq_true]
  rw [Finset.sum_insert hz, mv_binomial_basis_zero, mul_one] at he
  exact (mv_polynomial_binomial_expansion p D hp).trans he.symm

end Hindman168
