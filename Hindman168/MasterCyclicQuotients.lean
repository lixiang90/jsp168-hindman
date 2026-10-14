import Hindman168.CyclicScaleQuotients
import Hindman168.MasterParameterFamily

namespace Hindman168

theorem MasterParameterConditions.polynomial_cyclic_geometry
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A D F)
    (w l : ℕ) (f : MvPolynomial (Fin n) ℤ) (hf : f ∈ D) (x : Fin n → ℕ)
    (hx : ∀ i, x i ∈ primePool (F.pool w l).lower (F.pool w l).upper)
    (hz : MvPolynomial.eval (fun i => (x i : ℤ)) f ≠ 0) :
    let a := (MvPolynomial.eval (fun i => (x i : ℤ)) f).natAbs
    0 < a ∧ 0 < F.gap w l / (F.modulus w : ℕ) ∧
      a ∣ F.gap w l / (F.modulus w : ℕ) ∧
      F.gap w l / (F.modulus w : ℕ) =
        a * (F.gap w l / ((F.modulus w : ℕ) * a)) := by
  dsimp only
  let a := (MvPolynomial.eval (fun i => (x i : ℤ)) f).natAbs
  have ha : 0 < a := Int.natAbs_pos.mpr hz
  have hM := (F.modulus w).pos
  have hP : 0 < (F.modulus w : ℕ) * a := Nat.mul_pos hM ha
  have hPR := hF.gap_polynomial_dvd w l f hf x hx hz
  have hMP : (F.modulus w : ℕ) ∣ (F.modulus w : ℕ) * a := dvd_mul_right _ _
  have he := cyclicScale_factorization (F.modulus w) ((F.modulus w : ℕ) * a)
    (F.gap w l) hM hP hMP hPR
  rw [Nat.mul_div_cancel_left a hM] at he
  exact ⟨ha, Nat.div_pos (Nat.le_of_dvd (hF.gap_positive w l) (hF.gap_modulus_dvd w l)) hM,
    ⟨_, he⟩, he⟩

theorem MasterParameterConditions.polynomial_cyclic_subgroup_card
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A D F)
    (w l : ℕ) (f : MvPolynomial (Fin n) ℤ) (hf : f ∈ D) (x : Fin n → ℕ)
    (hx : ∀ i, x i ∈ primePool (F.pool w l).lower (F.pool w l).upper)
    (hz : MvPolynomial.eval (fun i => (x i : ℤ)) f ≠ 0)
    [Fintype (multipleAddSubgroup (ZMod (F.gap w l / (F.modulus w : ℕ)))
      (MvPolynomial.eval (fun i => (x i : ℤ)) f).natAbs)] :
    Fintype.card (multipleAddSubgroup (ZMod (F.gap w l / (F.modulus w : ℕ)))
      (MvPolynomial.eval (fun i => (x i : ℤ)) f).natAbs) =
        F.gap w l / ((F.modulus w : ℕ) * (MvPolynomial.eval (fun i => (x i : ℤ)) f).natAbs) := by
  obtain ⟨ha, hm, hd, he⟩ := hF.polynomial_cyclic_geometry w l f hf x hx hz
  rw [multipleDivisorSubgroup_card _ _ hm ha hd, he, Nat.mul_div_cancel_left _ ha]

end Hindman168
