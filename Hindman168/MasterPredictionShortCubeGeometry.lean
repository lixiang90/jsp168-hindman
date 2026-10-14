import Hindman168.MasterShortCubeRemainder
import Hindman168.MasterPredictionModulusGeometry

namespace Hindman168
open Filter
open scoped Topology

theorem cyclicScale_full_factorization (M P R : ℕ) (hMP : M ∣ P) (hPR : P ∣ R) :
    M * ((P / M) * (R / P)) = R ∧ M * (P / M) = P := by
  have he : M * (P / M) = P := Nat.mul_div_cancel' hMP
  constructor
  · rw [← mul_assoc, he, Nat.mul_div_cancel' hPR]
  · exact he

theorem MasterParameterConditions.samePool_prediction_short_lengths
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (gap : ℕ → Fin N)
    (f : MvPolynomial (Fin n) ℤ) (J B : ℕ) (hJ : 0 < J) :
    ∀ᶠ w in atTop, ∀ x : Fin n → ℕ,
      (∀ i, x i ∈ primePool (F.pool w (gap w).val).lower (F.pool w (gap w).val).upper) →
      MvPolynomial.eval (fun i => (x i : ℤ)) f ≠ 0 →
      B ≤ (F.gap w (gap w).val / (predictionCubeModulus w (F.modulus w) f x).natAbs) / J := by
  filter_upwards [hF.capped_short_lengths_eventually gap J
    (J + integerPolynomialCoeffSize f + f.totalDegree + 1) B hJ] with w hw
  intro x hx hz
  rw [cyclicScale_short_length]
  apply hw
  · exact Int.natAbs_pos.mpr (predictionCubeModulus_nonzero w (F.modulus w) f x (F.modulus w).pos hz)
  · apply predictionCubeModulus_polynomial_cap
    · have he := F.auxiliary_ge_two w (gap w).val
      omega
    · exact (F.modulus_le_auxiliary _ _).trans (Nat.le_add_left _ _)
    · intro i _
      have he := (Finset.mem_Ico.mp (Finset.mem_filter.mp (hx i)).1).2
      omega

theorem MasterParameterConditions.prediction_shortCube_geometry
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (gap : ℕ → Fin N)
    (f : MvPolynomial (Fin n) ℤ) (hf : f ∈ D) (J : ℕ) (hJ : 0 < J) :
    ∀ᶠ w in atTop, ∀ x : Fin n → ℕ,
      (∀ i, x i ∈ primePool (F.pool w (gap w).val).lower (F.pool w (gap w).val).upper) →
      MvPolynomial.eval (fun i => (x i : ℤ)) f ≠ 0 →
      let M := (F.modulus w : ℕ)
      let P := (predictionCubeModulus w M f x).natAbs
      let a := P / M
      let b := F.gap w (gap w).val / P
      0 < a ∧ 0 < b ∧ 0 < b / J ∧ M * (a * b) = F.gap w (gap w).val ∧ M * a = P := by
  filter_upwards [hF.samePool_prediction_short_lengths gap f J 1 hJ] with w hw
  intro x hx hz
  obtain ⟨hp, hm, hd, _⟩ := hF.predictionModulus_cyclic_geometry w (gap w).val f hf x hx hz
  have ha := Nat.div_pos (Nat.le_of_dvd hp hm) (F.modulus w).pos
  have hb := Nat.div_pos (Nat.le_of_dvd (hF.gap_positive w (gap w).val) hd) hp
  have hlen := hw x hx hz
  exact ⟨ha, hb, by omega, cyclicScale_full_factorization _ _ _ hm hd⟩

end Hindman168
