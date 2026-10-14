import Hindman168.ScalarMvSmallValuesPositiveNonconstant

namespace Hindman168
open scoped BigOperators Classical

/-- Actual positive-epsilon multivariable inverse INCLUDING the original
constant, with one fixed budget and original large-N threshold. -/
theorem scalar_mv_small_values_positive (n D B : ℕ) (hB : 0 < B)
    (δ : ℝ) (hδ : 0 < δ)
    (hcoarse : ∀ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ D → ∀ N : ℕ, 0 < N →
      ∀ ε : ℝ, ε ≤ δ/10 →
        δ*((scalarMvIntegerCube (Fin n) N).card : ℝ) ≤
          ((scalarMvIntegerCube (Fin n) N).filter (fun x => ‖scalarMvCircleOrbit p x‖ ≤ ε)).card →
        ∃ q : ℕ, 0 < q ∧ q ≤ B ∧ ∀ I : Fin n → ℕ, 0 < (∑ j, I j) →
          (N : ℝ)^(∑ j, I j)*‖(((q : ℝ)*MvPolynomial.coeff
            (Finsupp.equivFunOnFinite.symm I) p : ℝ) : UnitAddCircle)‖ ≤ (B : ℝ)) :
    ∃ A T : ℕ, 0 < A ∧ 0 < T ∧ ∀ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ D →
      ∀ N : ℕ, T ≤ N → ∀ ε : ℝ, 0 < ε → ε ≤ δ/10 →
        δ*((scalarMvIntegerCube (Fin n) N).card : ℝ) ≤
          ((scalarMvIntegerCube (Fin n) N).filter (fun x => ‖scalarMvCircleOrbit p x‖ ≤ ε)).card →
        ∃ q : ℕ, 0 < q ∧ q ≤ A ∧ ∀ I : Fin n → ℕ,
          (N : ℝ)^(∑ j, I j)*‖(((q : ℝ)*MvPolynomial.coeff
            (Finsupp.equivFunOnFinite.symm I) p : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)*ε := by
  obtain ⟨S, T, C, hS, hT, hC, hinv⟩ := scalar_mv_small_values_positive_nonconstant n D B hB δ hδ hcoarse
  let U := roughSpatialDegreeIndices (Fin n) D
  let A := S+⌈C⌉₊+⌈(S : ℝ)+(U.card : ℝ)*C⌉₊+1
  have hA : 0 < A := by dsimp only [A]; omega
  have hSA : S ≤ A := by dsimp only [A]; omega
  have hCA : C ≤ A := (Nat.le_ceil _).trans (by
    exact_mod_cast (show ⌈C⌉₊ ≤ A by dsimp only [A]; omega))
  have hConstA : (S : ℝ)+(U.card : ℝ)*C ≤ A := (Nat.le_ceil _).trans (by
    exact_mod_cast (show ⌈(S : ℝ)+(U.card : ℝ)*C⌉₊ ≤ A by dsimp only [A]; omega))
  refine ⟨A, T, hA, hT, ?_⟩
  intro p hp N hTN ε hε hεsmall hdense
  obtain ⟨q, hq, hqS, hcoeff⟩ := hinv p hp N hTN ε hε hεsmall hdense
  have hN : 0 < N := hT.trans_le hTN
  obtain ⟨x, hx, hsmall⟩ := scalar_mv_integer_cube_dense_sample p N hN δ ε hδ hdense
  have hconst := scalar_mv_small_value_constant_recovery p D N q hp x hx ε C hsmall hcoeff
  have hqSr : (q : ℝ) ≤ S := by exact_mod_cast hqS
  have hconstA : ‖(((q : ℝ)*MvPolynomial.coeff 0 p : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)*ε := by
    have hh := mul_le_mul_of_nonneg_right hqSr hε.le
    have hb := mul_le_mul_of_nonneg_right hConstA hε.le
    nlinarith only [hconst, hh, hb]
  refine ⟨q, hq, hqS.trans hSA, ?_⟩
  intro I
  by_cases hz : (∑ j, I j)=0
  · have hi : ∀ j, I j=0 := fun j => by
      have hh := Finset.single_le_sum (fun k _ => Nat.zero_le (I k)) (Finset.mem_univ j)
      omega
    have hI : Finsupp.equivFunOnFinite.symm I = 0 := by
      ext j
      simpa only [Finsupp.coe_equivFunOnFinite_symm, Finsupp.coe_zero, Pi.zero_apply] using hi j
    simpa only [hz, hI, pow_zero, one_mul] using hconstA
  · by_cases hID : (∑ j, I j) ≤ D
    · exact (hcoeff I (by omega) hID).trans (mul_le_mul_of_nonneg_right hCA hε.le)
    · rw [scalar_mv_coefficient_zero_above_degree p D hp I (Nat.lt_of_not_ge hID),
        mul_zero, AddCircle.coe_zero, norm_zero, mul_zero]
      positivity

end Hindman168
