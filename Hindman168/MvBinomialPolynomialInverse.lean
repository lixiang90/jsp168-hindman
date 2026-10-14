import Hindman168.MvBinomialCoefficientModOne
import Hindman168.TorusMvPolynomialInverse

namespace Hindman168
open scoped BigOperators Classical Topology

/-- Genuine scalar observable inverse in the ACTUAL multivariate binomial
basis. One SAME multiplier controls all ORIGINAL positive binomial coefficients. -/
theorem scalar_mv_binomial_observable_inverse (n D : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ B : ℕ, 0 < B ∧ ∀ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ D →
      ∀ N : ℕ, 0 < N → ∀ F ∈ unitLipschitzObservables UnitAddCircle,
        δ ≤ ‖unitCircleFiniteDiscrepancy (scalarMvIntegerCube (Fin n) N) (scalarMvCircleOrbit p) F‖ →
        ∃ q : ℕ, 0 < q ∧ q ≤ B ∧ ∀ I : Fin n → ℕ, 0 < (∑ j, I j) →
          (N : ℝ)^(∑ j, I j)*‖(((q : ℝ)*mvPolynomialBinomialCoefficient p D I : ℝ) :
            UnitAddCircle)‖ ≤ (B : ℝ) := by
  obtain ⟨A, hA, hinv⟩ := scalar_mv_polynomial_observable_inverse n D δ hδ
  let T := mvBinomialCoefficientBudget (Fin n) D
  let B := T*A+A
  have hB : 0 < B := by dsimp only [B]; omega
  have hAB : A ≤ B := by dsimp only [B]; omega
  have hbudget : (T : ℝ)*(A : ℝ) ≤ B := by exact_mod_cast Nat.le_add_right (T*A) A
  refine ⟨B, hB, ?_⟩
  intro p hp N hN F hF hbad
  obtain ⟨q, hq, hqA, hcoeff⟩ := hinv p hp N hN F hF hbad
  refine ⟨q, hq, hqA.trans hAB, ?_⟩
  intro I hI
  by_cases hID : (∑ j, I j) ≤ D
  · have h := mv_binomial_coefficient_mod_one p D q 1 I (mv_binomial_box_mem_of_weight_le D I hID)
      hI (N : ℝ) (A : ℝ) (by exact_mod_cast hN) (Nat.cast_nonneg A)
      (fun J _ hJ => hcoeff J hJ)
    exact h.trans hbudget
  · rw [mv_binomial_coefficient_zero_above_degree p D hp I (Nat.lt_of_not_ge hID),
      mul_zero, AddCircle.coe_zero, norm_zero, mul_zero]
    positivity

/-- Genuine original large-box small-value inverse in the ACTUAL binomial
basis, INCLUDING the constant and epsilon=0 with one fixed bound and SAME q. -/
theorem scalar_mv_binomial_small_values_inverse (n D : ℕ) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ B : ℕ, 0 < B ∧ ∀ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ D →
      ∀ N : ℕ, B ≤ N → ∀ ε : ℝ, 0 ≤ ε → ε ≤ δ/10 →
        δ*((scalarMvIntegerCube (Fin n) N).card : ℝ) ≤
          ((scalarMvIntegerCube (Fin n) N).filter (fun x => ‖scalarMvCircleOrbit p x‖ ≤ ε)).card →
        ∃ q : ℕ, 0 < q ∧ q ≤ B ∧ ∀ I : Fin n → ℕ,
          (N : ℝ)^(∑ j, I j)*‖(((q : ℝ)*mvPolynomialBinomialCoefficient p D I : ℝ) :
            UnitAddCircle)‖ ≤ (B : ℝ)*ε := by
  obtain ⟨A, hA, hinv⟩ := scalar_mv_polynomial_small_values_inverse n D δ hδ hδ1
  let T := mvBinomialCoefficientBudget (Fin n) D
  let B := T*A+A
  have hB : 0 < B := by dsimp only [B]; omega
  have hAB : A ≤ B := by dsimp only [B]; omega
  have hbudget : (T : ℝ)*(A : ℝ) ≤ B := by exact_mod_cast Nat.le_add_right (T*A) A
  refine ⟨B, hB, ?_⟩
  intro p hp N hBN ε hε hεsmall hdense
  have hAN := hAB.trans hBN
  have hN : 0 < N := hA.trans_le hAN
  obtain ⟨q, hq, hqA, hcoeff⟩ := hinv p hp N hAN ε hε hεsmall hdense
  refine ⟨q, hq, hqA.trans hAB, ?_⟩
  intro I
  by_cases hID : (∑ j, I j) ≤ D
  · have h := mv_binomial_coefficient_mod_one p D q 0 I (mv_binomial_box_mem_of_weight_le D I hID)
      (Nat.zero_le _) (N : ℝ) ((A : ℝ)*ε) (by exact_mod_cast hN) (by positivity)
      (fun J _ _ => hcoeff J)
    calc
      _ ≤ (T : ℝ)*((A : ℝ)*ε) := h
      _ = ((T : ℝ)*(A : ℝ))*ε := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hbudget hε
  · rw [mv_binomial_coefficient_zero_above_degree p D hp I (Nat.lt_of_not_ge hID),
      mul_zero, AddCircle.coe_zero, norm_zero, mul_zero]
    positivity

/-- Genuine standard TARGET-torus inverse in the EXACT binomial basis of
the corrected equal-cube theorem. The same actual nonzero horizontal
character controls EVERY original positive binomial coefficient. -/
theorem torus_mv_binomial_observable_inverse (m n D : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ B : ℕ, 0 < B ∧ ∀ p : Fin m → MvPolynomial (Fin n) ℝ,
      (∀ j, (p j).totalDegree ≤ D) → ∀ N : ℕ, 0 < N →
        ∀ F ∈ unitLipschitzObservables (UnitAddTorus (Fin m)),
          δ ≤ ‖unitTorusFiniteDiscrepancy (scalarMvIntegerCube (Fin n) N)
            (torusMvPolynomialOrbit p) F‖ →
          ∃ v : Fin m → ℤ, v ≠ 0 ∧ (∑ j, (v j).natAbs) ≤ B ∧
            ∀ I : Fin n → ℕ, 0 < (∑ i, I i) →
              (N : ℝ)^(∑ i, I i)*‖((∑ j, (v j : ℝ)*mvPolynomialBinomialCoefficient
                (p j) D I : ℝ) : UnitAddCircle)‖ ≤ (B : ℝ) := by
  obtain ⟨A, hA, hinv⟩ := torus_mv_polynomial_observable_inverse m n D δ hδ
  let T := mvBinomialCoefficientBudget (Fin n) D
  let B := T*A+A
  have hB : 0 < B := by dsimp only [B]; omega
  have hAB : A ≤ B := by dsimp only [B]; omega
  have hbudget : (T : ℝ)*(A : ℝ) ≤ B := by exact_mod_cast Nat.le_add_right (T*A) A
  refine ⟨B, hB, ?_⟩
  intro p hp N hN F hF hbad
  obtain ⟨v, hv, hvA, hcoeff⟩ := hinv p hp N hN F hF hbad
  refine ⟨v, hv, hvA.trans hAB, ?_⟩
  intro I hI
  rw [← mv_binomial_character_projection_coefficient]
  let P := torusPolynomialCharacterProjection p v
  have hP : P.totalDegree ≤ D := torus_polynomial_character_projection_degree p v D hp
  by_cases hID : (∑ j, I j) ≤ D
  · have h := mv_binomial_coefficient_mod_one P D 1 1 I (mv_binomial_box_mem_of_weight_le D I hID)
      hI (N : ℝ) (A : ℝ) (by exact_mod_cast hN) (Nat.cast_nonneg A)
      (fun J _ hJ => by
        simpa only [Nat.cast_one, one_mul, P, torus_polynomial_character_projection_coefficient] using hcoeff J hJ)
    have hb : (N : ℝ)^(∑ j, I j)*‖((mvPolynomialBinomialCoefficient P D I : ℝ) : UnitAddCircle)‖ ≤
        (T : ℝ)*(A : ℝ) := by simpa only [Nat.cast_one, one_mul] using h
    exact hb.trans hbudget
  · rw [mv_binomial_coefficient_zero_above_degree P D hP I (Nat.lt_of_not_ge hID),
      AddCircle.coe_zero, norm_zero, mul_zero]
    positivity

end Hindman168
