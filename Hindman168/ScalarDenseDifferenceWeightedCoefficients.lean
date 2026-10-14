import Hindman168.ScalarDifferenceSecondCoefficient

/-! Genuine dense second-coefficient separation. The actual inverse of
small values is applied to the CONSTRUCTED polynomial in the shift. -/
namespace Hindman168
open Polynomial
open scoped Classical

theorem scalar_dense_difference_weighted_coefficients (D : ℕ) (δ A : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 0 ≤ A) :
    ∃ B T : ℕ, 0 < B ∧ 0 < T ∧
      ∀ P Q : ℝ[X], Q.natDegree ≤ D → ∀ (σ : ℕ → ℝ) (N : ℕ), T ≤ N →
        ∀ U : Finset ℕ, U ⊆ Finset.range N → δ*(N : ℝ) ≤ U.card →
        (∀ h ∈ U, (N : ℝ)^2*‖((scalarDifferencePolynomial P Q h (σ h)).coeff 2 : UnitAddCircle)‖ ≤ A) →
        ∃ q : ℕ, 0 < q ∧ q ≤ B ∧ ∀ j : ℕ, 3 ≤ j → j ≤ D →
          (N : ℝ)^j*‖(((q : ℝ)*(j.choose 2 : ℝ)*Q.coeff j : ℝ) : UnitAddCircle)‖ ≤ (B : ℝ)*A := by
  obtain ⟨B,hB,hInv⟩ := polynomial_small_values_inverse D δ hδ hδ1
  let T := B+⌈10*A/δ⌉₊+1
  refine ⟨B,T,hB,by dsimp [T]; omega,?_⟩
  intro P Q hQ σ N hTN U hU hdense hcoeff
  have hBN : B ≤ N := by dsimp [T] at hTN; omega
  have hN : 0 < N := hB.trans_le hBN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hceil : 10*A/δ ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈10*A/δ⌉₊ ≤ N from by dsimp [T] at hTN; omega))
  have hnum : 10*A ≤ δ*(N : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ hδ).mp hceil
  let ε : ℝ := A/(N : ℝ)^2
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hεsmall : ε ≤ δ/10 := by
    dsimp only [ε]
    apply (div_le_iff₀ (pow_pos hNr 2)).mpr
    have hs : (N : ℝ) ≤ (N : ℝ)^2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hs hδ.le
    nlinarith
  have hsub : U ⊆ (Finset.range N).filter (fun h : ℕ =>
      ‖(((scalarDifferenceSecondFamily P Q).eval (h : ℝ) : ℝ) : UnitAddCircle)‖ ≤ ε) := by
    intro h hh
    apply Finset.mem_filter.mpr
    refine ⟨hU hh,?_⟩
    rw [scalar_difference_second_family_eval P Q h (σ h)]
    apply (le_div_iff₀ (pow_pos hNr 2)).mpr
    simpa only [mul_comm] using hcoeff h hh
  have hcount : δ*(N : ℝ) ≤ ((Finset.range N).filter (fun h : ℕ =>
      ‖(((scalarDifferenceSecondFamily P Q).eval (h : ℝ) : ℝ) : UnitAddCircle)‖ ≤ ε)).card :=
    hdense.trans (by exact_mod_cast Finset.card_le_card hsub)
  obtain ⟨q,hq,hqB,hBounds⟩ := hInv (scalarDifferenceSecondFamily P Q)
    (scalar_difference_second_family_degree P Q D hQ) N hBN ε hε hεsmall hcount
  refine ⟨q,hq,hqB,?_⟩
  intro j hj hjD
  have he : j-2+2=j := by omega
  have hb := hBounds (j-2) (by omega)
  rw [scalar_difference_second_family_coefficient P Q (j-2) (by omega),he] at hb
  rw [← mul_assoc] at hb
  have hpower : (N : ℝ)^j = (N : ℝ)^2*(N : ℝ)^(j-2) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    _ = (N : ℝ)^2*((N : ℝ)^(j-2)*‖(((q : ℝ)*(j.choose 2 : ℝ)*Q.coeff j : ℝ) : UnitAddCircle)‖) := by
      rw [hpower]
      ring
    _ ≤ (N : ℝ)^2*((B : ℝ)*ε) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by dsimp only [ε]; field_simp [hNr.ne']

end Hindman168
