import Hindman168.PolynomialRowIntegerTranslations
import Hindman168.MasterChainExcess

/-! Exact integer quotients preserve units at arbitrary residue moduli. -/

namespace Hindman168

open scoped Classical

theorem natExactQuotient_residue_isUnit {M d q : ℕ} (hd : d ∣ M)
    (hM : IsUnit (M : ZMod q)) : IsUnit ((M / d : ℕ) : ZMod q) := by
  have he : ((M / d : ℕ) : ZMod q) * (d : ZMod q) = (M : ZMod q) := by
    simpa only [Nat.cast_mul] using
      congrArg (fun z : ℕ => (z : ZMod q)) (Nat.div_mul_cancel hd)
  exact isUnit_of_mul_isUnit_left (he.symm ▸ hM)

theorem natDivisor_residue_isUnit {M d q : ℕ} (hd : d ∣ M)
    (hM : IsUnit (M : ZMod q)) : IsUnit (d : ZMod q) := by
  have he : ((M / d : ℕ) : ZMod q) * (d : ZMod q) = (M : ZMod q) := by
    simpa only [Nat.cast_mul] using
      congrArg (fun z : ℕ => (z : ZMod q)) (Nat.div_mul_cancel hd)
  exact isUnit_of_mul_isUnit_right (he.symm ▸ hM)

theorem intExactQuotient_residue_isUnit {D d : ℤ} {q : ℕ} (hd : d ∣ D)
    (hD : IsUnit (D : ZMod q)) : IsUnit ((D / d : ℤ) : ZMod q) := by
  have he : ((D / d : ℤ) : ZMod q) * (d : ZMod q) = (D : ZMod q) := by
    simpa only [Int.cast_mul] using
      congrArg (fun z : ℤ => (z : ZMod q)) (Int.ediv_mul_cancel hd)
  exact isUnit_of_mul_isUnit_left (he.symm ▸ hD)

theorem intSign_residue_isUnit {D : ℤ} {q : ℕ} (hD : D ≠ 0) :
    IsUnit (D.sign : ZMod q) := by
  rcases lt_or_gt_of_ne hD with hneg | hpos
  · simp [Int.sign_eq_neg_one_of_neg hneg]
  · simp [Int.sign_eq_one_of_pos hpos]

theorem normalizedIntegerCoordinate_residue_isUnit (W M c cstar w e q : ℕ)
    (D d b : ℤ) (hD : D ≠ 0) (hdiv : d ∣ D)
    (habs : W ^ (e + 1) * c ∣ M)
    (hS : smoothPartNat w D.natAbs ∣ W ^ (e - 1))
    (hM : IsUnit (M : ZMod q)) (hcstar : IsUnit (cstar : ZMod q))
    (hDu : IsUnit (D : ZMod q)) (hb : IsUnit (b : ZMod q)) :
    IsUnit (normalizedIntegerCoordinate M c cstar w D d b : ZMod q) := by
  have hquot := natExactQuotient_residue_isUnit
    (absorbed_smooth_quotient W M c _ e habs hS).1 hM
  have hcofactor := intExactQuotient_residue_isUnit hdiv hDu
  simpa only [normalizedIntegerCoordinate, Int.cast_mul, Int.cast_natCast] using
    ((((intSign_residue_isUnit hD).mul hquot).mul hcstar).mul hb).mul hcofactor

theorem normalizedRootIntegerCoordinate_residue_isUnit (M c cstar q : ℕ)
    (b : ℤ) (hdiv : c ∣ M) (hM : IsUnit (M : ZMod q))
    (hcstar : IsUnit (cstar : ZMod q)) (hb : IsUnit (b : ZMod q)) :
    IsUnit (normalizedRootIntegerCoordinate M c cstar b : ZMod q) := by
  simpa only [normalizedRootIntegerCoordinate, Int.cast_mul, Int.cast_natCast] using
    ((natExactQuotient_residue_isUnit hdiv hM).mul hcstar).mul hb

theorem MasterParameterConditions.modulus_residue_isUnit {n N : ℕ} {A : Finset ℚ}
    {T : Finset (MvPolynomial (Fin n) ℤ)} {master : MasterParameterFamily}
    (hF : MasterParameterConditions N A T master) (w q : ℕ)
    (hq : (primorial w).Coprime q) : IsUnit ((master.modulus w : ℕ) : ZMod q) := by
  obtain ⟨e, he⟩ := hF.smooth_modulus w
  rw [he]
  exact (ZMod.isUnit_iff_coprime _ q).mpr (hq.pow_left e)

end Hindman168
