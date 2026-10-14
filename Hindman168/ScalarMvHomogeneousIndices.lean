import Hindman168.ScalarMvLineHomogeneous
import Hindman168.LeibmanMonomialVectors

namespace Hindman168
open scoped BigOperators Classical

/-- Fixed homogeneous degree-r indices, independent of polynomial coefficients. -/
noncomputable def scalarMvHomogeneousIndices (κ : Type*) [Fintype κ] (r : ℕ) :
    Finset (κ → ℕ) :=
  (Fintype.piFinset (fun _ : κ => Finset.range (r+1))).filter (fun I => (∑ j, I j)=r)

theorem scalar_mv_homogeneous_indices_mem {κ : Type*} [Fintype κ]
    (r : ℕ) (I : κ → ℕ) : I ∈ scalarMvHomogeneousIndices κ r ↔ (∑ j, I j)=r := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, h⟩
    intro j
    apply Finset.mem_range.mpr
    have hj := Finset.single_le_sum (fun k _ => Nat.zero_le (I k)) (Finset.mem_univ j)
    omega

/-- The actual line-coefficient constant on a FIXED homogeneous index set.
All missing original coefficients are genuinely zero, rather than assumed. -/
theorem scalar_mv_line_constant_fixed_indices {κ : Type*} [Fintype κ]
    (p : MvPolynomial κ ℝ) (u : κ → ℝ) (r : ℕ) :
    MvPolynomial.coeff 0 (scalarMvLineCoefficient p u r) =
      ∑ I ∈ scalarMvHomogeneousIndices κ r,
        MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I) p*∏ j, u j^(I j) := by
  let S := scalarMvHomogeneousIndices κ r
  let T := S.map Finsupp.equivFunOnFinite.symm.toEmbedding
  have hT (I : κ →₀ ℕ) : I ∈ T ↔ (∑ j, I j)=r := by
    constructor
    · intro h
      obtain ⟨J, hJ, rfl⟩ := Finset.mem_map.mp h
      simpa only [Equiv.toEmbedding_apply, Finsupp.coe_equivFunOnFinite_symm] using
        (scalar_mv_homogeneous_indices_mem r J).mp hJ
    · intro h
      refine Finset.mem_map.mpr ⟨Finsupp.equivFunOnFinite I, ?_,
        Finsupp.equivFunOnFinite.symm_apply_apply I⟩
      apply (scalar_mv_homogeneous_indices_mem r _).mpr
      exact h
  have hsub : p.support.filter (fun I => (∑ j, I j)=r) ⊆ T :=
    fun I hI => (hT I).mpr (Finset.mem_filter.mp hI).2
  have he : (∑ I ∈ p.support.filter (fun I => (∑ j, I j)=r),
      MvPolynomial.coeff I p*∏ j, u j^(I j)) =
      ∑ I ∈ T, MvPolynomial.coeff I p*∏ j, u j^(I j) := by
    apply Finset.sum_subset hsub
    intro I hI hnot
    have hz : I ∉ p.support := by
      intro hmem
      exact hnot (Finset.mem_filter.mpr ⟨hmem, (hT I).mp hI⟩)
    rw [MvPolynomial.notMem_support_iff.mp hz, zero_mul]
  rw [scalar_mv_line_coefficient_constant, he]
  simp only [T, S, Finset.sum_map, Equiv.toEmbedding_apply, Finsupp.coe_equivFunOnFinite_symm]

theorem scalar_mv_line_constant_monomial_vector {n : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (u : Fin n → ℝ) (r : ℕ) :
    MvPolynomial.coeff 0 (scalarMvLineCoefficient p u r) =
      ∑ I : ↥(scalarMvHomogeneousIndices (Fin n) r),
        MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I.val) p*
          leibmanMonomialVector (scalarMvHomogeneousIndices (Fin n) r) u I := by
  rw [scalar_mv_line_constant_fixed_indices]
  exact (Finset.sum_coe_sort (scalarMvHomogeneousIndices (Fin n) r)
    (fun I => MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I) p*∏ j, u j^(I j))).symm

theorem scalar_mv_coefficient_zero_above_degree {κ : Type*} [Fintype κ]
    (p : MvPolynomial κ ℝ) (D : ℕ) (hp : p.totalDegree ≤ D) (I : κ → ℕ)
    (hI : D < ∑ j, I j) : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I) p = 0 := by
  apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
  change p.totalDegree < (Finsupp.equivFunOnFinite.symm I).sum (fun _ e => e)
  have hs : (Finsupp.equivFunOnFinite.symm I).sum (fun _ e => e) = ∑ j, I j := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Finsupp.coe_equivFunOnFinite_symm]
  rw [hs]
  exact hp.trans_lt hI

end Hindman168
