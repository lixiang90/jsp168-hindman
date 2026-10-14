import Hindman168.MasterPredictionModulusCap

namespace Hindman168

theorem predictionCubeModulus_natAbs_dvd {r : ℕ} (w s M : ℕ)
    (hs : s ∣ M) (f : MvPolynomial (Fin r) ℤ) (x : Fin r → ℕ) :
    (predictionCubeModulus w s f x).natAbs ∣
      M * (MvPolynomial.eval (fun j => (x j : ℤ)) f).natAbs := by
  rw [predictionCubeModulus_natAbs]
  exact Nat.mul_dvd_mul hs (roughPartNat_dvd_value _ _)

theorem MasterParameterConditions.predictionModulus_gap_dvd
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A D F)
    (w l s : ℕ) (hs : s ∣ (F.modulus w : ℕ))
    (f : MvPolynomial (Fin n) ℤ) (hf : f ∈ D) (x : Fin n → ℕ)
    (hx : ∀ i, x i ∈ primePool (F.pool w l).lower (F.pool w l).upper)
    (hz : MvPolynomial.eval (fun i => (x i : ℤ)) f ≠ 0) :
    (predictionCubeModulus w s f x).natAbs ∣ F.gap w l :=
  (predictionCubeModulus_natAbs_dvd w s (F.modulus w) hs f x).trans
    (hF.gap_polynomial_dvd w l f hf x hx hz)

theorem predictionCubeModulus_master_factor {r : ℕ} (w M : ℕ)
    (f : MvPolynomial (Fin r) ℤ) (x : Fin r → ℕ) :
    M ∣ (predictionCubeModulus w M f x).natAbs := by
  rw [predictionCubeModulus_natAbs]
  exact dvd_mul_right _ _

theorem MasterParameterConditions.predictionModulus_cyclic_geometry
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A D F)
    (w l : ℕ) (f : MvPolynomial (Fin n) ℤ) (hf : f ∈ D) (x : Fin n → ℕ)
    (hx : ∀ i, x i ∈ primePool (F.pool w l).lower (F.pool w l).upper)
    (hz : MvPolynomial.eval (fun i => (x i : ℤ)) f ≠ 0) :
    let P := (predictionCubeModulus w (F.modulus w) f x).natAbs
    0 < P ∧ (F.modulus w : ℕ) ∣ P ∧ P ∣ F.gap w l ∧
      F.gap w l / (F.modulus w : ℕ) =
        (P / (F.modulus w : ℕ)) * (F.gap w l / P) := by
  dsimp only
  have hp := Int.natAbs_pos.mpr (predictionCubeModulus_nonzero w (F.modulus w) f x
    (F.modulus w).pos hz)
  have hm := predictionCubeModulus_master_factor w (F.modulus w) f x
  have hd := hF.predictionModulus_gap_dvd w l (F.modulus w) (dvd_refl _) f hf x hx hz
  exact ⟨hp, hm, hd, cyclicScale_factorization _ _ _ (F.modulus w).pos hp hm hd⟩

end Hindman168
