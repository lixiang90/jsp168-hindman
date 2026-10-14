import Hindman168.ScalarMvSmallValuesPositive
import Hindman168.FiniteUniformErrorZero

namespace Hindman168
open scoped BigOperators Classical

/-- Complete actual large-box small-value estimate from the actual coarse
estimate, INCLUDING all original coefficients and epsilon=0. The finite
candidate minimum closes zero tolerance with a genuinely uniform bound. -/
theorem scalar_mv_small_value_estimate_from_coarse (n D B : ℕ) (hB : 0 < B)
    (δ : ℝ) (hδ : 0 < δ)
    (hcoarse : ∀ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ D → ∀ N : ℕ, 0 < N →
      ∀ ε : ℝ, ε ≤ δ/10 →
        δ*((scalarMvIntegerCube (Fin n) N).card : ℝ) ≤
          ((scalarMvIntegerCube (Fin n) N).filter (fun x => ‖scalarMvCircleOrbit p x‖ ≤ ε)).card →
        ∃ q : ℕ, 0 < q ∧ q ≤ B ∧ ∀ I : Fin n → ℕ, 0 < (∑ j, I j) →
          (N : ℝ)^(∑ j, I j)*‖(((q : ℝ)*MvPolynomial.coeff
            (Finsupp.equivFunOnFinite.symm I) p : ℝ) : UnitAddCircle)‖ ≤ (B : ℝ)) :
    ∃ K : ℕ, 0 < K ∧ ScalarMvSmallValueEstimate (Fin n) D δ K := by
  obtain ⟨A, T, hA, hT, hpositive⟩ := scalar_mv_small_values_positive n D B hB δ hδ hcoarse
  let K := A+T+1
  have hK : 0 < K := by dsimp only [K]; omega
  have hAK : A ≤ K := by dsimp only [K]; omega
  refine ⟨K, hK, ?_⟩
  intro p hp N hKN ε hε hεsmall hdense
  have hTN : T ≤ N := by dsimp only [K] at hKN; omega
  have hN : 0 < N := hT.trans_le hTN
  by_cases hz : ε=0
  · subst ε
    let U := roughSpatialDegreeIndices (Fin n) D
    let V := insert (0 : Fin n → ℕ) U
    let s := Finset.Icc 1 A
    have hs : s.Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hA⟩⟩
    let f := fun q : ℕ => fun I : Fin n → ℕ =>
      (N : ℝ)^(∑ j, I j)*‖(((q : ℝ)*MvPolynomial.coeff
        (Finsupp.equivFunOnFinite.symm I) p : ℝ) : UnitAddCircle)‖
    have hsmall : ∀ ε' : ℝ, 0 < ε' → ε' ≤ δ/10 → ∃ q ∈ s, ∀ I ∈ V, f q I ≤ (A : ℝ)*ε' := by
      intro ε' hε' hε'small
      have hsub : ((scalarMvIntegerCube (Fin n) N).filter (fun x => ‖scalarMvCircleOrbit p x‖ ≤ 0)) ⊆
          (scalarMvIntegerCube (Fin n) N).filter (fun x => ‖scalarMvCircleOrbit p x‖ ≤ ε') := by
        intro x hx
        have hv := Finset.mem_filter.mp hx
        exact Finset.mem_filter.mpr ⟨hv.1, hv.2.trans hε'.le⟩
      have hd : δ*((scalarMvIntegerCube (Fin n) N).card : ℝ) ≤
          ((scalarMvIntegerCube (Fin n) N).filter (fun x => ‖scalarMvCircleOrbit p x‖ ≤ ε')).card :=
        hdense.trans (by exact_mod_cast Finset.card_le_card hsub)
      obtain ⟨q, hq, hqA, hcoeff⟩ := hpositive p hp N hTN ε' hε' hε'small hd
      exact ⟨q, Finset.mem_Icc.mpr ⟨hq, hqA⟩, fun I _ => hcoeff I⟩
    obtain ⟨q, hq, hzero⟩ := finite_uniform_error_zero s hs V f
      (fun _ _ _ _ => by dsimp only [f]; positivity)
      (δ/10) (A : ℝ) (by positivity) (by exact_mod_cast hA) hsmall
    have hb := Finset.mem_Icc.mp hq
    refine ⟨q, hb.1, hb.2.trans hAK, ?_⟩
    intro I
    by_cases hID : (∑ j, I j) ≤ D
    · have hIV : I ∈ V := by
        by_cases hzI : (∑ j, I j)=0
        · have hi : ∀ j, I j=0 := fun j => by
            have hh := Finset.single_le_sum (fun k _ => Nat.zero_le (I k)) (Finset.mem_univ j)
            omega
          have he : I=0 := funext hi
          exact Finset.mem_insert.mpr (Or.inl he)
        · exact Finset.mem_insert_of_mem ((rough_spatial_degree_indices_mem D I).mpr ⟨by omega, hID⟩)
      have he := hzero I hIV
      change (N : ℝ)^(∑ j, I j)*‖(((q : ℝ)*MvPolynomial.coeff
        (Finsupp.equivFunOnFinite.symm I) p : ℝ) : UnitAddCircle)‖ = 0 at he
      rw [he, mul_zero]
    · rw [scalar_mv_coefficient_zero_above_degree p D hp I (Nat.lt_of_not_ge hID),
        mul_zero, AddCircle.coe_zero, norm_zero, mul_zero, mul_zero]
  · have hεpos : 0 < ε := lt_of_le_of_ne hε (Ne.symm hz)
    obtain ⟨q, hq, hqA, hcoeff⟩ := hpositive p hp N hTN ε hεpos hεsmall hdense
    refine ⟨q, hq, hqA.trans hAK, ?_⟩
    intro I
    exact (hcoeff I).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hAK) hε)

end Hindman168
